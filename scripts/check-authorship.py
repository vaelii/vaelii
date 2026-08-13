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
    url = path if path.startswith("http") else f"{API}{path}"
    req = urllib.request.Request(url, headers={
        "Accept": accept,
        "Authorization": f"Bearer {token}",
        "X-GitHub-Api-Version": "2022-11-28",
        "User-Agent": "vaelii-authorship-gate",
    })
    with urllib.request.urlopen(req) as r:
        return json.loads(r.read().decode()), r.headers.get("Link", "")


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


def raw_roster(repo, ref, token):
    blob, _ = api(f"/repos/{repo}/contents/{ROSTER_PATH}?ref={ref}", token,
                  accept="application/vnd.github.raw")
    return blob if isinstance(blob, str) else ""


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
        who = f"{self.name} <{self.email}>" if self.name else f"<{self.email}>"
        return f"{who}  ({self.login})" if self.login else who


def collect(commits):
    """Every party a commit names: who wrote it, who applied it, who it credits."""
    found = {}

    def add(name, email, login, where):
        if not (email or login):
            return
        # One person, one row. The same identity reaches us in two shapes: an
        # author or committer carries a resolved GitHub login beside the git
        # email, while a trailer carries the email alone. Keying on the email
        # merges the pair, so a contributor is not reported twice and a login
        # learned from one occurrence explains all of them.
        key = email or f"login:{login.lower()}"
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
    return reasons


def die(msg):
    print(f"authorship gate: {msg}", file=sys.stderr)
    sys.exit(2)


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
    args = ap.parse_args()

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
        # branch itself is behind protection. Nothing to say.
        print("authorship gate: no pull request in this event, nothing to check.")
        return 0

    meta, _ = api(f"/repos/{args.repo}/pulls/{pr}", token)
    base = base or meta["base"]["ref"]
    commits = api_paged(f"/repos/{args.repo}/pulls/{pr}/commits?per_page=100", token)

    print(f"authorship gate — {args.repo}#{pr}  {meta['title']}")
    print(f"  base {base}, {len(commits)} commit(s), roster {ROSTER_PATH}@{base}")
    print()

    if len(commits) >= 250:
        print("  NOTE: GitHub caps this endpoint at 250 commits. Rebase or split the")
        print("        pull request so every commit is readable.")
        print()

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

    admitted, blocked = [], []
    for ident in idents:
        hit = (ident.login.lower() in logins) or (ident.email in emails)
        (admitted if hit else blocked).append(ident)

    for ident in sorted(admitted, key=lambda i: i.label()):
        owner = owner_of.get(ident.login.lower()) or owner_of.get(ident.email) or "?"
        print(f"  ok       {ident.label()}  [{owner}]")
    if admitted and blocked:
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
