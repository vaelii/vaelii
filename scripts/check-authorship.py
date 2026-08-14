#!/usr/bin/env python3
"""The authorship gate: every identity on a pull request is an admitted person.

CONTRIBUTING.md §7 holds that a `Signed-off-by:` may only name someone who can
make the certification, and that a co-author trailer is human-only. The other
two gates cannot check that. cla-assistant confirms an account completed an
OAuth flow; the DCO app matches a trailer string against the commit's author
field. Both are string matchers, and neither can ask whether the named party is
a person.

So this check decides by roster, not by inspection. Every author, committer and
trailer on the pull request must appear in `.github/AUTHORS.roster` on the base
branch, which only a maintainer can write. An account nobody has admitted fails
closed, whatever it is and whatever it says about itself.

An author or committer is matched on the **login** GitHub resolved, never on the
git email beside it: an email is whatever its author set it to, so admitting a
commit because its email is on the roster would let an unadmitted account walk in
under an admitted one's address. The email arm is for trailers, which carry an
email and no account. A trailer carrying neither — a bare `Co-authored-by: Name`
with no `<address>` — matches nothing and is blocked, which is the point: it
names a party the roster has no way to admit.

`--selftest` runs the roster and matching rules against synthetic commits and
needs no network. `lein lint` runs it, so a regression in either shows up before
a pull request meets it.

The heuristics in MARKERS never decide the outcome. They run on a blocked
identity to say *why* it looks the way it does, so the failure names something
actionable instead of a bare login. An account that announces nothing about
itself is blocked exactly as firmly as one whose bio says "construct" — the
roster is the gate, and self-description is only ever an explanation.

Run it locally against a live pull request:

    GITHUB_TOKEN=$(gh auth token) python3 scripts/check-authorship.py --pr 27
"""

import argparse
import json
import os
import re
import sys
import tempfile
import urllib.error
import urllib.request
from datetime import datetime, timezone

ROSTER_PATH = ".github/AUTHORS.roster"

API = os.environ.get("GITHUB_API_URL", "https://api.github.com").rstrip("/")

# The three trailers that carry a certification or a credit. `Signed-off-by:` is
# the DCO itself; the co-author pair is what GitHub reads to attribute a commit.
TRAILER_RE = re.compile(
    r"^[ \t]*(Signed-off-by|Co-authored-by|Co-developed-by)[ \t]*:[ \t]*(.+?)[ \t]*$",
    re.IGNORECASE | re.MULTILINE,
)
IDENT_RE = re.compile(r"^(?P<name>.*?)[ \t]*<(?P<email>[^>]+)>$")

# Explanations, not tests. Each pattern is checked against the login, the display
# name and the profile bio of an identity the roster already rejected.
MARKERS = [
    (r"\[bot\]$", "login ends in [bot], so this is a GitHub App"),
    (r"\bconstruct\b", "describes itself as a construct"),
    (r"\b(shared hands|distinct handwriting|this handwriting)\b",
     "describes itself as operated by someone else"),
    (r"\b(bot|automaton|daemon|golem|homunculus)\b", "names itself after a machine"),
    (r"\b(ai|llm|gpt|claude|gemini|agent|assistant|synthetic|artificial)\b",
     "names itself after a language model or agent"),
]
MARKERS = [(re.compile(p, re.IGNORECASE), why) for p, why in MARKERS]

# A fresh account with no history is not evidence of anything on its own — every
# person has a first week. It is printed to give a maintainer something to weigh,
# and it is never the reason a check fails.
YOUNG_DAYS = 180


def api(path, token, accept="application/vnd.github+json"):
    """One request. Parsed as JSON unless the caller asked for something else.

    `application/vnd.github.raw` returns the file's own bytes rather than a JSON
    envelope around them, so parsing every response the same way makes the roster
    read — the one call that uses it — a `JSONDecodeError` on the first line of
    the file. Reading the accept header here is what lets `load_roster` receive
    the text it asked for.
    """
    url = path if path.startswith("http") else f"{API}{path}"
    req = urllib.request.Request(url, headers={
        "Accept": accept,
        "Authorization": f"Bearer {token}",
        "X-GitHub-Api-Version": "2022-11-28",
        "User-Agent": "vaelii-authorship-gate",
    })
    with urllib.request.urlopen(req) as r:
        body, link = r.read().decode(), r.headers.get("Link", "")
    if "raw" in accept:
        return body, link
    return json.loads(body), link


def api_paged(path, token):
    out, link = [], None
    url = path
    while url:
        page, link = api(url, token)
        out.extend(page)
        url = None
        for part in link.split(","):
            if 'rel="next"' in part:
                url = part.split(";")[0].strip().strip("<>")
    return out


def load_roster(repo, ref, token, local=None):
    """Read the roster from the base branch, never from the checkout.

    A pull request can edit any file in its own tree, so a roster read from the
    working copy would let a contributor admit themselves in the same change the
    roster is meant to gate. Reading it at `ref` means the only writable copy is
    the one behind branch protection.

    `local` is for running the gate by hand against a roster that is not on the
    branch yet. CI never passes it.
    """
    if local:
        with open(local) as f:
            text = f.read()
    else:
        try:
            blob, _ = api(f"/repos/{repo}/contents/{ROSTER_PATH}?ref={ref}", token,
                          accept="application/vnd.github.raw")
        except urllib.error.HTTPError as e:
            if e.code == 404:
                die(f"no {ROSTER_PATH} on {ref}. The gate fails closed without one.")
            raise
        text = blob if isinstance(blob, str) else json.dumps(blob)
    logins, emails, owner_of = set(), set(), {}
    for line in text.splitlines():
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        tokens = line.split()
        owner = tokens[0]
        for tok in tokens:
            key = tok.lower()
            if "@" in tok:
                emails.add(key)
            else:
                logins.add(key)
            owner_of[key] = owner
    return logins, emails, owner_of


class Identity:
    def __init__(self, name, email, login, where):
        self.name = (name or "").strip()
        self.email = (email or "").strip().lower()
        self.login = (login or "").strip()
        self.where = [where]

    @property
    def key(self):
        return (self.login.lower(), self.email)

    def label(self):
        if self.email:
            who = f"{self.name} <{self.email}>" if self.name else f"<{self.email}>"
        else:
            who = self.name or "(unnamed)"
        return f"{who}  ({self.login})" if self.login else who


def admitted(ident, logins, emails):
    """Is this identity on the roster?

    One rule, and which arm applies is decided by what the identity carries
    rather than by trying both. A login is what GitHub resolved for the account
    that pushed, so where there is one it is the fact worth checking. An email is
    self-asserted — `git config user.email` takes anything — so it stands in only
    where there is no account to check: a trailer. Trying both would let the arm
    nobody has to earn decide the ones they do.
    """
    if ident.login:
        return ident.login.lower() in logins
    if ident.email:
        return ident.email in emails
    return False


def collect(commits):
    """Every party a commit names: who wrote it, who applied it, who it credits."""
    found = {}

    def add(name, email, login, where):
        if not (email or login or name):
            return
        # One person, one row. The same identity reaches us in two shapes: an
        # author or committer carries a resolved GitHub login beside the git
        # email, while a trailer carries the email alone. Keying on the email
        # merges the pair, so a contributor is not reported twice and a login
        # learned from one occurrence explains all of them.
        #
        # A name alone is the third shape and it is kept rather than dropped: a
        # `Co-authored-by: Name` with no `<address>` still names a party, and a
        # party the roster cannot admit is the answer this gate exists to give.
        # Discarding it here would report green on the trailer §7 most often has
        # to refuse.
        key = email or (f"login:{login.lower()}" if login else f"name:{name.lower()}")
        prior = found.get(key)
        if prior:
            prior.where.append(where)
            if login and not prior.login:
                prior.login = login
            if name and not prior.name:
                prior.name = name
        else:
            found[key] = Identity(name, email, login, where)

    for c in commits:
        sha = c["sha"][:8]
        detail = c.get("commit", {})
        for role in ("author", "committer"):
            git_side = detail.get(role) or {}
            gh_side = c.get(role) or {}
            add(git_side.get("name"), git_side.get("email"),
                (gh_side or {}).get("login"), f"{sha} {role}")
        for kind, value in TRAILER_RE.findall(detail.get("message", "")):
            m = IDENT_RE.match(value.strip())
            if not m:
                add(value.strip(), "", "", f"{sha} {kind}")
                continue
            add(m.group("name"), m.group("email"), "", f"{sha} {kind}")
    return list(found.values())


def explain(ident, token):
    """Say what a blocked identity looks like. Advisory, never decisive."""
    reasons = []
    profile = {}
    if ident.login:
        try:
            profile, _ = api(f"/users/{ident.login}", token)
        except urllib.error.HTTPError:
            profile = {}
    if profile.get("type") == "Bot":
        reasons.append("GitHub reports this account's type as Bot")
    haystack = " ".join(filter(None, [
        ident.login, ident.name, profile.get("name"), profile.get("bio"),
    ]))
    for pat, why in MARKERS:
        if pat.search(haystack):
            reasons.append(why)
    bio = (profile.get("bio") or "").strip()
    if bio:
        reasons.append(f'bio: "{bio[:150]}"')
    created = profile.get("created_at")
    if created:
        age = (datetime.now(timezone.utc)
               - datetime.fromisoformat(created.replace("Z", "+00:00"))).days
        if age < YOUNG_DAYS:
            reasons.append(
                f"account is {age} days old, {profile.get('followers', 0)} followers, "
                f"{profile.get('public_repos', 0)} public repos")
    if not ident.login and ident.email:
        reasons.append("appears only as a trailer, with no GitHub account behind it")
    if not ident.login and not ident.email:
        reasons.append("a trailer with no <address> — it credits a party that cannot "
                       "be resolved to anyone, so nothing can admit it")
    return reasons


def die(msg):
    print(f"authorship gate: {msg}", file=sys.stderr)
    sys.exit(2)


def selftest():
    """Exercise the two rules that decide a verdict, without a network.

    Both have a failure mode that reports success: an identity this file never
    collects is never blocked, and a match arm that is too generous admits. Each
    is invisible against a live pull request — the check goes green either way —
    so they are asked here, where a wrong answer is a failed lint rather than a
    merged commit.
    """
    def commit(msg, email="human@example.com", login="paceheart"):
        side = {"name": "A Person", "email": email}
        return {"sha": "0" * 40, "author": {"login": login},
                "committer": {"login": login},
                "commit": {"author": side, "committer": side, "message": msg}}

    logins, emails = {"paceheart"}, {"ubiquity@gmail.com"}

    def verdict(c):
        """(label, admitted?) for every identity on one commit."""
        return {i.label(): admitted(i, logins, emails) for i in collect([c])}

    cases = []

    def case(name, got, want):
        cases.append((name, got == want, got, want))

    # A trailer naming a party with no <address> is still a party. Dropping it is
    # a green verdict on the trailer §7 most often has to refuse.
    v = verdict(commit("t\n\nCo-authored-by: Some Agent"))
    case("bare-name co-author is collected", len(v), 2)
    case("bare-name co-author is blocked", v.get("Some Agent"), False)

    v = verdict(commit("t\n\nSigned-off-by: Some Agent"))
    case("bare-name sign-off is collected", len(v), 2)
    case("bare-name sign-off is blocked", v.get("Some Agent"), False)

    # An unadmitted account under an admitted address. The email is self-asserted,
    # so this is the arm that must not decide.
    v = verdict(commit("t", email="ubiquity@gmail.com", login="some-bot"))
    case("rostered email cannot admit an unrostered login",
         v.get("A Person <ubiquity@gmail.com>  (some-bot)"), False)

    # And the ordinary passes, so the rule above is not simply refusing everyone.
    v = verdict(commit("t", email="whatever@example.com", login="paceheart"))
    case("rostered login is admitted whatever the email",
         v.get("A Person <whatever@example.com>  (paceheart)"), True)

    v = verdict(commit("t\n\nCo-authored-by: P <ubiquity@gmail.com>"))
    case("rostered email admits a trailer", v.get("P <ubiquity@gmail.com>"), True)

    v = verdict(commit("t\n\nCo-authored-by: X <nobody@example.com>"))
    case("unrostered trailer is blocked", v.get("X <nobody@example.com>"), False)

    # Trailer parsing: the spellings a real message carries.
    v = verdict(commit("t\n\nco-authored-by:  P <ubiquity@gmail.com>  "))
    case("trailer match is case- and space-insensitive",
         v.get("P <ubiquity@gmail.com>"), True)

    # Roster parsing: comments stripped, tokens split by kind, case folded.
    text = "# comment\n\nAlice  ALICE@example.com  # inline\nbob\n"
    with tempfile.NamedTemporaryFile("w", suffix=".roster", delete=False) as f:
        f.write(text)
        path = f.name
    try:
        rl, re_, owner = load_roster("x/y", "main", "", local=path)
    finally:
        os.unlink(path)
    case("roster folds case and splits by kind", (rl, re_),
         ({"alice", "bob"}, {"alice@example.com"}))
    case("roster files every token under the first", owner.get("alice@example.com"), "Alice")

    # The roster arrives over the API as the file's own bytes — `load_roster` asks
    # for `application/vnd.github.raw` — and a reader that parses every response
    # as JSON turns the first line of the file into a traceback. `--roster` reads
    # a local path and never crosses that seam, so the case above cannot see it;
    # this one stubs the transport and does.
    class _Resp:
        def __init__(self, body):
            self._b, self.headers = body.encode(), {}

        def read(self):
            return self._b

        def __enter__(self):
            return self

        def __exit__(self, *_):
            return False

    real = urllib.request.urlopen
    urllib.request.urlopen = lambda *_a, **_k: _Resp("Alice  alice@example.com\n")
    try:
        got = load_roster("owner/repo", "develop", "token")[:2]
    except Exception as exc:                       # noqa: BLE001 — the failure IS the finding
        got = f"{type(exc).__name__}: {exc}"
    finally:
        urllib.request.urlopen = real
    case("roster loads from a raw API body", got, ({"alice"}, {"alice@example.com"}))

    width = max(len(n) for n, _, _, _ in cases)
    bad = 0
    for name, good, got, want in cases:
        print(f"  {'ok  ' if good else 'FAIL'}  {name.ljust(width)}"
              + ("" if good else f"   got {got!r}, want {want!r}"))
        bad += 0 if good else 1
    print()
    if bad:
        print(f"authorship selftest: {bad} of {len(cases)} failed", file=sys.stderr)
        return 1
    print(f"authorship selftest: {len(cases)} checks, all pass")
    return 0


def event_context():
    """Pull request number and base ref from the Actions event payload."""
    path = os.environ.get("GITHUB_EVENT_PATH")
    if not path or not os.path.exists(path):
        return None, None
    with open(path) as f:
        ev = json.load(f)
    pr = ev.get("pull_request")
    if not pr:
        return None, None
    return pr["number"], pr["base"]["ref"]


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--pr", type=int, help="pull request number (default: from the event)")
    ap.add_argument("--repo", default=os.environ.get("GITHUB_REPOSITORY"))
    ap.add_argument("--base", help="branch holding the roster (default: the PR's base)")
    ap.add_argument("--roster", help="read a local roster file instead of the base branch (by hand only)")
    ap.add_argument("--selftest", action="store_true",
                    help="check the roster and matching rules against synthetic commits; no network")
    args = ap.parse_args()

    if args.selftest:
        return selftest()

    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if not token:
        die("set GITHUB_TOKEN. The gate reads the pull request and the roster over the API.")
    if not args.repo:
        die("set --repo or GITHUB_REPOSITORY.")

    pr, base = args.pr, args.base
    if pr is None:
        pr, ev_base = event_context()
        base = base or ev_base
    if pr is None:
        # push, schedule or dispatch: there is no pull request to read, and the
        # branch itself is behind protection.
        #
        # Said at length because a green run here is the thing most likely to be
        # mistaken for the gate working. Dispatching the workflow is the obvious
        # way to try it, and a dispatch is exactly the event with no authorship
        # to read.
        print("authorship gate: no pull request in this event, so nothing was checked.")
        print("  A green run here is not the gate passing. It reads the commits of a")
        print("  pull request; a push, a schedule and a manual dispatch have none, and")
        print("  this run says only that it found none.")
        print("  To exercise it against real commits, pass --pr <n> with a GITHUB_TOKEN,")
        print("  or --selftest for the rules alone.")
        return 0

    meta, _ = api(f"/repos/{args.repo}/pulls/{pr}", token)
    base = base or meta["base"]["ref"]
    commits = api_paged(f"/repos/{args.repo}/pulls/{pr}/commits?per_page=100", token)

    print(f"authorship gate — {args.repo}#{pr}  {meta['title']}")
    print(f"  base {base}, {len(commits)} commit(s), roster {ROSTER_PATH}@{base}")
    print()

    # Refused, not noted. GitHub's commit list for a pull request stops at 250, so
    # past that the identities are simply unread — and a verdict over a prefix is
    # indistinguishable from one over the whole, which is the shape of every gate
    # that goes quietly green. Exit 2 is the same answer a missing roster gets: not
    # "these commits are fine", but "this cannot be checked".
    if len(commits) >= 250:
        die(f"GitHub caps this endpoint at 250 commits and this pull request reads "
            f"{len(commits)}, so any commit past that is unread and its authorship "
            f"unchecked. Rebase or split the pull request so every commit is readable.")

    logins, emails, owner_of = load_roster(args.repo, base, token, args.roster)

    # An org-wide roster, so a contributor admitted once is admitted everywhere.
    # Opt-in by setting ORG_ROSTER_REPO in the workflow, and only worth turning on
    # once that repo's default branch is protected: it is additive, so whoever can
    # write it can admit an account on every repo that reads it. Union, never
    # override — a repo's own roster stays sufficient on its own.
    org_repo = os.environ.get("ORG_ROSTER_REPO", "").strip()
    if org_repo:
        org_ref = api(f"/repos/{org_repo}", token)[0]["default_branch"]
        o_logins, o_emails, o_owner = load_roster(org_repo, org_ref, token)
        logins |= o_logins
        emails |= o_emails
        owner_of = {**o_owner, **owner_of}
        print(f"  plus org roster {ROSTER_PATH}@{org_repo}:{org_ref}")
        print()
    idents = collect(commits)

    ok, blocked = [], []
    for ident in idents:
        (ok if admitted(ident, logins, emails) else blocked).append(ident)

    for ident in sorted(ok, key=lambda i: i.label()):
        owner = owner_of.get(ident.login.lower()) or owner_of.get(ident.email) or "?"
        print(f"  ok       {ident.label()}  [{owner}]")
    if ok and blocked:
        print()

    for ident in sorted(blocked, key=lambda i: i.label()):
        print(f"  BLOCKED  {ident.label()}")
        print(f"           on: {', '.join(sorted(set(ident.where)))}")
        for reason in explain(ident, token):
            print(f"           {reason}")
        print()

    if not blocked:
        print()
        print(f"  Every identity on this pull request is on the roster. {len(idents)} checked.")
        return 0

    print("CONTRIBUTING.md §7: each commit's author is the person who signs it off, a")
    print("Signed-off-by: may only name someone who can make that certification, and a")
    print("co-author trailer is human-only. That rules out a tool, bot or agent account.")
    print()
    print("If the work is good and the authorship line is not, it is a rebase, not a")
    print("rejection: re-author the commits under the person who signs them off, drop")
    print("the trailers naming anyone else, and force-push.")
    print()
    print(f"A maintainer admits an account by adding one line to {ROSTER_PATH}")
    print(f"on {base}. Until then this check fails.")
    return 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except urllib.error.HTTPError as e:
        die(f"GitHub API {e.code} on {e.url}: {e.read().decode()[:200]}")
    except json.JSONDecodeError as e:
        # A response that did not parse is this script misreading the API, not a
        # verdict about the pull request. Exit 2 says which, where a traceback
        # says only that something went wrong somewhere.
        die(f"a GitHub response did not parse as JSON ({e}). The gate reached the "
            f"API and could not read it, so it has checked nothing.")
