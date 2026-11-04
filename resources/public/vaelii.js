/* vaelii — the browser's one hand-written script (docs/web.md).  htmx carries the
   declarative interactivity; this carries the things it cannot express:

     1. the header's two colour dots — the palette and the light/dark theme — held as
        data-* on <html> and persisted.  The pre-paint <head> script applies the saved
        values; this wires the dots and keeps what they say about themselves current.
        Marking the menubar link for the current path active belongs here too, since
        the header is outside the swapped region and no server answer re-renders it.
     2. folding a framed region away by its number — the digit in the top border, either
        clicked or pressed, the way a terminal monitor hides a box. Which regions are
        folded is held per path, so a page opens the way the reader left it.
     3. the `/kbs` page's option sliders, which show their own value as it moves.
     4. the browsing history: a term or sentex page carries a hidden `[data-visit]`
        element, recorded here in localStorage, and the front page's `#history` panel
        lists the terms, literals and rules visited, each in visit order.
     5. a sentex's menu: a right-click on a badge opens Copy / Edit / Remove at the
        pointer, the controls of the sentex page's action bar fetched from
        /sentex-actions.

   A sentex row carries no script.  The row is text, so a press-drag over it selects
   that text the way a press-drag over any other text does, and the row's `[edit]`
   link is an ordinary htmx GET of `/edit?handles=<h>` into the editor panel. */
(function () {
  "use strict";

  const $ = (s) => document.querySelector(s);
  const $$ = (s) => document.querySelectorAll(s);

  // localStorage throws outright in a locked-down browser, and one we cannot reach
  // just means the defaults.  A key reads; a key and a value writes.
  const stored = (k, v) => {
    try { return v === undefined ? localStorage.getItem(k) : localStorage.setItem(k, v); }
    catch (e) { return null; }
  };

  const closeEditor = () => { const e = $("#editor"); if (e) e.innerHTML = ""; };

  // ---- palette, theme, menubar -------------------------------------------

  const PALETTES = ["violet", "red", "green", "rainbow"];

  // what the OS is asking for, which is what a page with no stored theme is showing
  const osTheme = () => {
    try { return matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light"; }
    catch (e) { return "light"; }
  };

  // Both readers **validate**, because localStorage is shared ground that anything can
  // have written: a value outside the set is not a preference, it is noise, and reading
  // it back would set the page to a value no rule matches — which strands it off the OS
  // default rather than following it.  An unrecognised palette is the default one, and
  // an unrecognised theme is no stored choice at all.
  const palette = () => {
    const p = stored("vaelii-palette");
    return PALETTES.indexOf(p) < 0 ? "violet" : p;
  };
  const storedTheme = () => {
    const t = stored("vaelii-theme");
    return t === "light" || t === "dark" ? t : null;
  };

  // mirror what localStorage and the URL already say — each dot's title, the active
  // nav link.  Everything that changes one of them ends here.  The dots need no
  // state class: each is painted in the variables it sets, so it already shows it.
  function reflect() {
    const pal = $("#palette-dot"), thm = $("#theme-dot"), chosen = storedTheme();
    if (pal) pal.title = "Colour palette: " + palette() + " (click to change)";
    if (thm) {
      thm.title = chosen
        ? "Theme: " + chosen + " (click to flip)"
        : "Theme: " + osTheme() + ", following the system (click to choose one)";
    }
    $$(".menubar a, a.kb-active").forEach((a) => a.classList.toggle("active", a.getAttribute("href") === location.pathname));
  }

  // data-palette picks the accent pair, data-theme sets light or dark over the OS
  // preference — and a page that has never stored one carries no data-theme at all,
  // which is what leaves the stylesheet's media query in charge
  const apply = (k, v) => {
    document.documentElement.setAttribute("data-" + k, v);
    stored("vaelii-" + k, v);
    reflect();
  };

  // the OS flipping under an open page moves it too, until a click stores one; the CSS
  // does the recolouring on its own, so this is only the theme dot's title catching up
  try {
    matchMedia("(prefers-color-scheme: dark)").addEventListener("change", reflect);
  } catch (e) { /* no matchMedia: the page just never follows a live change */ }

  // ---- wiring ------------------------------------------------------------

  document.addEventListener("click", (ev) => {
    if (ev.target.closest("#sx-cancel")) return closeEditor();
    const nbtn = ev.target.closest("button.panel-n");
    if (nbtn) {
      const region = nbtn.closest("[data-panel]");
      if (region) { setFolded(region, !region.hasAttribute("data-folded")); return; }
    }
    if (ev.target.closest("#palette-dot")) {
      const i = PALETTES.indexOf(palette());
      return apply("palette", PALETTES[(i + 1) % PALETTES.length]);
    }
    // flip whichever theme is on screen, stored or OS-chosen, and the flip is what
    // turns it into a stored one
    if (ev.target.closest("#theme-dot")) {
      return apply("theme", (storedTheme() || osTheme()) === "dark" ? "light" : "dark");
    }
  });

  // ---- a sentex's menu ---------------------------------------------------

  // A right-click on a badge opens Copy / Edit / Remove for its sentex at the pointer:
  // the sentex page's action bar, fetched from /sentex-actions so the two are one
  // definition.  A press on an item hides the menu rather than removing it, so the
  // request the press started keeps its source element; a press elsewhere, Escape, a
  // scroll or the next swap of the page removes it.
  const closeSxMenu = () => { const m = $("#sx-menu"); if (m) m.remove(); };

  document.addEventListener("contextmenu", async (ev) => {
    const a = ev.target.closest && ev.target.closest("a.badge-link");
    const m = a && /\/sentex\/(\d+)/.exec(a.getAttribute("href") || "");
    if (!m) return;
    ev.preventDefault();
    closeSxMenu();
    const menu = document.createElement("div");
    menu.id = "sx-menu";
    menu.style.left = ev.clientX + "px";
    menu.style.top = ev.clientY + "px";
    document.body.append(menu);
    try {
      const r = await fetch("/sentex-actions?h=" + m[1], { headers: { "HX-Request": "true" } });
      if (!r.ok || !menu.isConnected) return closeSxMenu();
      menu.innerHTML = await r.text();
      if (window.htmx) htmx.process(menu);
      // kept inside the viewport: a badge near the right or bottom edge opens it leftward
      // or upward
      const b = menu.getBoundingClientRect();
      if (b.right > innerWidth) menu.style.left = Math.max(0, innerWidth - b.width - 4) + "px";
      if (b.bottom > innerHeight) menu.style.top = Math.max(0, innerHeight - b.height - 4) + "px";
      const first = menu.querySelector("button");
      if (first) first.focus();
    } catch (e) { closeSxMenu(); }
  });
  document.addEventListener("click", (ev) => {
    const menu = $("#sx-menu");
    if (!menu) return;
    if (!menu.contains(ev.target)) return closeSxMenu();
    if (ev.target.closest("a, button")) menu.hidden = true;
  });
  document.addEventListener("keydown", (ev) => { if (ev.key === "Escape") closeSxMenu(); });
  document.addEventListener("scroll", closeSxMenu, { passive: true });
  document.addEventListener("htmx:afterSettle", () => { const m = $("#sx-menu"); if (m && m.hidden) m.remove(); });

  // ---- folding a framed region ------------------------------------------

  // Folded regions are remembered per path, so opening the front page again shows the
  // shape the reader left it in.  The value is a plain list of digits; anything else in
  // the key is noise some other writer left and is read as nothing folded.
  const foldKey = () => "vaelii-folded:" + location.pathname;
  const foldedSet = () => new Set((stored(foldKey()) || "").split(",").filter((d) => /^[1-9][0-9]?$/.test(d)));

  function setFolded(el, folded) {
    el.toggleAttribute("data-folded", folded);
    const btn = el.querySelector("button.panel-n");
    if (btn) btn.setAttribute("aria-expanded", folded ? "false" : "true");
    const n = el.getAttribute("data-panel"), set = foldedSet();
    if (folded) set.add(n); else set.delete(n);
    stored(foldKey(), [...set].join(","));
  }

  const fold = (n) => {
    const el = $('[data-panel="' + n + '"]');
    if (el) setFolded(el, !el.hasAttribute("data-folded"));
  };

  // re-applied after every swap: a fetched region arrives unfolded whatever the reader
  // last said about it
  function reflectFolds() {
    const set = foldedSet();
    $$("[data-panel]").forEach((el) => {
      const folded = set.has(el.getAttribute("data-panel"));
      el.toggleAttribute("data-folded", folded);
      const btn = el.querySelector("button.panel-n");
      if (btn) btn.setAttribute("aria-expanded", folded ? "false" : "true");
    });
  }

  // Escape closes the editor and a digit folds a region, wherever the focus is — except
  // in a field, where both keys are the reader typing.  A reader who opened the editor
  // from a row has not moved the page, so closing it must not either.
  document.addEventListener("keydown", (ev) => {
    if (ev.key === "Escape") {
      const ed = $("#editor");
      if (ed && ed.innerHTML) { closeEditor(); ev.preventDefault(); }
      return;
    }
    if (ev.altKey || ev.ctrlKey || ev.metaKey || !/^[1-9]$/.test(ev.key)) return;
    const t = ev.target;
    if (t && (t.isContentEditable || /^(INPUT|TEXTAREA|SELECT)$/.test(t.tagName))) return;
    if ($('[data-panel="' + ev.key + '"]')) { fold(ev.key); ev.preventDefault(); }
  });

  // ---- browsing history -------------------------------------------------

  // Three lists, each in visit order with the latest visit last.  A revisit moves the
  // entry to the end, and each list keeps its latest HISTORY_CAP entries.
  const HISTORY_KEY = "vaelii-history";
  const HISTORY_CAP = 50;
  const HISTORY_KINDS = [["term", "Terms"], ["literal", "Literals"], ["rule", "Rules"]];

  // localStorage is shared ground, so an entry is kept only when its href is one of the
  // two page shapes and its class is a role class: anything else would put a foreign
  // link or class on the page
  const validEntry = (e) =>
    e && typeof e.label === "string" && typeof e.href === "string" &&
    /^\/(term\?q=|sentex\/[0-9]+$)/.test(e.href) &&
    (e.cls == null || /^t-[a-z]+$/.test(e.cls));

  function readHistory() {
    let h = {};
    try { h = JSON.parse(stored(HISTORY_KEY) || "{}") || {}; } catch (e) { h = {}; }
    const out = {};
    HISTORY_KINDS.forEach(([k]) => {
      out[k] = Array.isArray(h[k]) ? h[k].filter(validEntry).slice(-HISTORY_CAP) : [];
    });
    return out;
  }
  const writeHistory = (h) => stored(HISTORY_KEY, JSON.stringify(h));

  function recordVisit() {
    const m = $("#main [data-visit]");
    if (!m) return;
    const kind = m.getAttribute("data-visit");
    const e = { href: m.getAttribute("data-href"), label: m.getAttribute("data-label"),
                cls: m.getAttribute("data-class") || null };
    const h = readHistory();
    if (!h[kind] || !validEntry(e)) return;
    h[kind] = h[kind].filter((x) => x.href !== e.href).concat([e]).slice(-HISTORY_CAP);
    writeHistory(h);
  }

  function removeVisit(kind, href) {
    const h = readHistory();
    if (!h[kind]) return;
    h[kind] = h[kind].filter((x) => x.href !== href);
    writeHistory(h);
    renderHistory();
  }

  const termQ = (e) => new URLSearchParams(e.href.slice("/term".length)).get("q");
  const handleOf = (e) => e.href.slice("/sentex/".length);
  const HANDLE_KINDS = ["literal", "rule"];

  // The history is recorded against whichever KB was active at the visit, so once per
  // panel drawn the server says which entries the active KB holds (`/history/known`) and
  // the rest are forgotten.  Only an entry that was asked about is dropped: one recorded
  // while the answer was on its way stays.  A KB still loading is not judged
  // (`complete: false`), since what it lacks may not have arrived yet.
  function pruneHistory(panel) {
    if (panel.dataset.pruned) return;
    panel.dataset.pruned = "1";
    const h = readHistory();
    const terms = h.term.map(termQ);
    const handles = HANDLE_KINDS.flatMap((k) => h[k].map(handleOf));
    if (!terms.length && !handles.length) return;
    const qs = terms.map((q) => "t=" + encodeURIComponent(q))
      .concat(["handles=" + handles.join(",")]).join("&");
    fetch("/history/known?" + qs)
      .then((r) => (r.ok ? r.json() : Promise.reject(r.status)))
      .then((known) => {
        if (!known.complete) return;
        const askedT = new Set(terms), keptT = new Set(known.terms);
        const askedH = new Set(handles), keptH = new Set(known.handles.map(String));
        const now = readHistory();
        now.term = now.term.filter((e) => !askedT.has(termQ(e)) || keptT.has(termQ(e)));
        HANDLE_KINDS.forEach((k) => {
          now[k] = now[k].filter((e) => !askedH.has(handleOf(e)) || keptH.has(handleOf(e)));
        });
        writeHistory(now);
        renderHistory();
      })
      .catch(() => {});
  }

  // built from elements and textContent, never from markup, since every label came out
  // of localStorage
  function renderHistory() {
    const panel = $("#history"), body = panel && panel.querySelector(".history-body");
    if (!body) return;
    pruneHistory(panel);
    const h = readHistory();
    body.replaceChildren();
    HISTORY_KINDS.forEach(([kind, title]) => {
      if (!h[kind].length) return;
      const row = document.createElement("div");
      row.className = "history-row";
      const head = document.createElement("span");
      head.className = "history-kind muted";
      head.textContent = title;
      row.appendChild(head);
      // a literal or a rule is drawn by the server (`/history/sentexes`), with its badge,
      // its colours and its belief now; the text entries below stand until it answers
      const items = document.createElement("div");
      items.className = "history-items";
      row.appendChild(items);
      if (kind !== "term") {
        items.classList.add("history-sentexes");
        items.setAttribute("hx-get", "/history/sentexes?handles=" +
          h[kind].map((e) => e.href.slice("/sentex/".length)).join(","));
        items.setAttribute("hx-trigger", "load");
        // the body's boosted-navigation target, select and swap would put the fragment
        // in place of #main
        items.setAttribute("hx-target", "this");
        items.setAttribute("hx-select", "unset");
        items.setAttribute("hx-swap", "innerHTML");
      }
      h[kind].forEach((e) => {
        const item = document.createElement("span");
        item.className = "history-item";
        const a = document.createElement("a");
        a.className = "sx" + (e.cls ? " " + e.cls : "");
        a.href = e.href;
        a.title = e.label;
        a.textContent = e.label;
        const x = document.createElement("button");
        x.type = "button";
        x.className = "history-x";
        x.setAttribute("aria-label", "remove " + e.label + " from the history");
        x.dataset.kind = kind;
        x.dataset.href = e.href;
        x.textContent = "×";
        item.append(a, x);
        items.appendChild(item);
      });
      body.appendChild(row);
    });
    panel.hidden = !body.children.length;
    if (window.htmx) window.htmx.process(body);
  }

  document.addEventListener("click", (ev) => {
    const x = ev.target.closest("button.history-x");
    if (x) removeVisit(x.dataset.kind, x.dataset.href);
  });

  // the header is outside #main, so a boosted navigation swaps the page under it and
  // leaves the active menubar link pointing at where the reader used to be
  document.addEventListener("htmx:afterSwap", (ev) => {
    // the history's own literal row arriving is not a navigation, and rendering the
    // history again would fetch that row again, without end
    const t = ev.detail && ev.detail.target;
    if (t && t.closest && t.closest("#history")) return;
    reflect(); reflectFolds(); recordVisit(); renderHistory();
  });

  // A 400 into #main is a page: the one a route renders for a parameter it cannot read,
  // naming the parameter.  htmx swaps only a 2xx unless told otherwise, so a page's own
  // form sending a value its route refuses would answer with nothing on screen.  Only a
  // swap into #main: a continuation row and the editor panel keep what they hold.
  document.addEventListener("htmx:beforeSwap", (ev) => {
    const d = ev.detail;
    if (d.xhr && d.xhr.status === 400 && d.target && d.target.id === "main") {
      d.shouldSwap = true;
      d.isError = false;
    }
  });

  const setPalette = (p) => apply("palette", p);
  const setTheme = (t) => apply("theme", t);
  window.vaelii = { closeEditor, setPalette, setTheme, fold };
  const start = () => { reflect(); reflectFolds(); recordVisit(); renderHistory(); };
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", start);
  else start();
})();

// ---- the KB catalog's sliders (/kbs) ------------------------------------
// A knob is three elements: the range input the reader drags (0–1000, a position,
// not a value), the <output> that shows what that position means, and the hidden
// field the form actually submits.  The mapping lives here and in `slider-pos`
// server-side, and the two agree: linear for the small knobs, logarithmic for the
// counts that run to millions, where every interesting value would otherwise sit in
// the first few pixels of a linear track.
//
// Only a drag syncs.  The server renders the default's position, its readout, and
// its exact value together, so leaving them alone until the reader moves something
// keeps a default exactly the number the generator documents rather than whatever
// the position happens to round back to.
(() => {
  const valueAt = (r) => {
    const lo = +r.dataset.min, hi = +r.dataset.max, step = +r.dataset.step || 1;
    const t = (+r.value) / 1000;
    const raw = r.dataset.log === "1"
      ? Math.expm1(Math.log1p(lo) + t * (Math.log1p(hi) - Math.log1p(lo)))
      : lo + t * (hi - lo);
    return Math.min(hi, Math.max(lo, Math.round(raw / step) * step));
  };

  document.addEventListener("input", (ev) => {
    const r = ev.target.closest && ev.target.closest(".knob-r");
    if (!r) return;
    const v = valueAt(r);
    const knob = r.closest(".knob");
    const out = knob && knob.querySelector(".knob-v");
    const hid = knob && knob.querySelector("[data-knob-value]");
    if (out) out.textContent = v.toLocaleString() + (r.dataset.unit || "");
    if (hid) hid.value = v;
  });
})();

// ---- the sentence editor (/edit, /assert, /levels) ----------------------
// A `.ed` is three elements over one value: the <textarea> that holds the text and takes
// the keys, the <pre class="ed-hl"> painted behind it (transparent text over a coloured
// copy, so the caret and the selection are the browser's own), and the <ul> of
// completions dropped under the caret.  A page with no script still has the textarea,
// which is why the value lives there and nowhere else.
//
// Four jobs htmx cannot express, all of them keyed on the caret:
//
//   1. Rainbow parens.  Each delimiter is coloured by its nesting depth, cycling through
//      six, and one with nothing to close is coloured as the error it is.  Strings,
//      numbers, `?variables`, `:keywords` and `;comments` take their own colour, and a
//      symbol standing alone at the top level takes the context colour, because that is
//      what the server reads it as.  The scan is the same one `indentAt` walks, so the
//      picture and the indentation can never disagree about where a string ends.
//   2. Indentation.  Enter opens the next line under the enclosing form's **first
//      argument** (Lisp's own rule) or one past its paren when the form has none, and Tab
//      re-indents the line the caret is on.  Both read the delimiters to the left of the
//      caret; neither needs the parse the server does.
//   3. Completion.  The symbol before the caret is a prefix; `/complete` answers the
//      terms it could become, off the KB's term-name set.  Tab and Enter take the
//      highlighted one, the arrows move, Escape closes the list without closing the
//      editor.
//   4. Submitting a one-line editor.  The goal box is a `rows="1"` editor, so Enter has
//      to submit the form rather than open a line inside it.
(() => {
  "use strict";

  const OPEN = "([{", CLOSE = ")]}";
  const DELIM = /[\s()[\]{}";]/;
  const DEPTHS = 6;                  // the paren colours, cycled

  // ---- one scan, used by the painter and by the indenter ----------------
  // `at` is called for every token with {kind, start, end, depth}; kinds are
  // "open" "close" "str" "num" "var" "kw" "cmt" "sym" "ws".
  function scan(text, at, stop) {
    let i = 0, depth = 0;
    const n = stop === undefined ? text.length : stop;
    while (i < n) {
      const c = text[i];
      if (c === ";") {
        let j = text.indexOf("\n", i); if (j < 0 || j > n) j = n;
        at("cmt", i, j, depth); i = j; continue;
      }
      if (c === '"') {
        let j = i + 1;
        while (j < n && text[j] !== '"') j += text[j] === "\\" ? 2 : 1;
        j = Math.min(j + 1, n);
        at("str", i, j, depth); i = j; continue;
      }
      if (OPEN.indexOf(c) >= 0) { at("open", i, i + 1, depth); depth++; i++; continue; }
      if (CLOSE.indexOf(c) >= 0) { depth--; at("close", i, i + 1, depth); if (depth < 0) depth = 0; i++; continue; }
      if (/\s/.test(c)) {
        let j = i; while (j < n && /\s/.test(text[j])) j++;
        at("ws", i, j, depth); i = j; continue;
      }
      let j = i; while (j < n && !DELIM.test(text[j])) j++;
      const word = text.slice(i, j);
      const kind = word[0] === "?" ? "var"
        : word[0] === ":" ? "kw"
          : /^[+-]?\d/.test(word) ? "num" : "sym";
      at(kind, i, j, depth); i = j;
    }
  }

  const esc = (s) => s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");

  function paint(ed) {
    const ta = ed.querySelector(".ed-in"), code = ed.querySelector(".ed-code");
    if (!ta || !code) return;
    const text = ta.value;
    let html = "";
    scan(text, (kind, start, end, depth) => {
      const body = esc(text.slice(start, end));
      if (kind === "ws") { html += body; return; }
      if (kind === "open" || kind === "close") {
        const cls = depth < 0 ? "ed-bad" : "ed-p" + (depth % DEPTHS);
        html += '<span class="' + cls + '">' + body + "</span>";
        return;
      }
      // a symbol standing alone at the top level is a context line, not a term inside a
      // sentence, and the server reads it as one — so it takes the context colour
      const cls = kind === "sym" && depth === 0 ? "ed-ctx" : "ed-" + kind;
      html += '<span class="' + cls + '">' + body + "</span>";
    });
    // a trailing newline collapses in a <pre>, so the last line has nothing to sit on
    code.innerHTML = html + "\n";
    code.parentNode.scrollTop = ta.scrollTop;
    code.parentNode.scrollLeft = ta.scrollLeft;
  }

  // The column the next line opens at: under the enclosing form's first argument, or one
  // past its opening paren when the form has none on the line above.
  function indentAt(text, pos) {
    const stack = [];                // {col, argCol, seen} per open delimiter
    let lineStart = 0;
    const element = (start) => {
      const top = stack[stack.length - 1];
      if (!top) return;
      top.seen++;
      if (top.seen === 2 && top.argCol === null) top.argCol = start - lineStart;
    };
    scan(text, (kind, start, end) => {
      if (kind === "ws" || kind === "cmt") {
        const nl = text.lastIndexOf("\n", end - 1);
        if (nl >= start - 1 && nl >= 0 && nl < end) lineStart = nl + 1;
        return;
      }
      if (kind === "open") { element(start); stack.push({ col: start - lineStart, argCol: null, seen: 0 }); return; }
      if (kind === "close") { stack.pop(); return; }
      element(start);
    }, pos);
    const top = stack[stack.length - 1];
    if (!top) return 0;
    return top.argCol !== null ? top.argCol : top.col + 1;
  }

  const lineStartOf = (text, pos) => text.lastIndexOf("\n", pos - 1) + 1;

  function replace(ta, from, to, insert, caret) {
    ta.setRangeText(insert, from, to, "end");
    if (caret !== undefined) ta.selectionStart = ta.selectionEnd = caret;
    ta.dispatchEvent(new Event("input", { bubbles: true }));
  }

  // ---- completion --------------------------------------------------------

  const listOf = (ed) => ed.querySelector(".ed-complete");
  const prefixAt = (ta) => {
    const m = /[^\s()[\]{}";]+$/.exec(ta.value.slice(0, ta.selectionStart));
    return m ? m[0] : "";
  };

  function closeList(ed) {
    const ul = listOf(ed);
    if (ul) { ul.hidden = true; ul.innerHTML = ""; }
  }

  function highlight(ul, i) {
    const items = Array.from(ul.children);
    items.forEach((li, k) => li.classList.toggle("on", k === i));
    ul.dataset.i = String(i);
  }

  let pending = 0;
  function suggest(ed) {
    const ta = ed.querySelector(".ed-in");
    const ul = listOf(ed);
    if (!ta || !ul) return;
    const q = prefixAt(ta);
    if (q.length < 2 || q[0] === "?" || q[0] === ":") return closeList(ed);
    const seq = ++pending;
    // a plain fetch: the query is the symbol at the caret, which is not a field htmx can
    // include, and the list it fills carries no hx attributes of its own
    fetch("/complete?q=" + encodeURIComponent(q), { headers: { "HX-Request": "true" } })
      .then((r) => (r.ok ? r.text() : ""))
      .then((html) => {
        if (seq !== pending) return;                  // a later keystroke already won
        if (!html.trim()) return closeList(ed);
        ul.innerHTML = html;
        ul.hidden = false;
        highlight(ul, 0);
      })
      .catch(() => closeList(ed));
  }

  function accept(ed) {
    const ta = ed.querySelector(".ed-in"), ul = listOf(ed);
    if (!ta || !ul || ul.hidden) return false;
    const li = ul.children[+(ul.dataset.i || 0)];
    if (!li) return false;
    const q = prefixAt(ta), start = ta.selectionStart - q.length;
    const term = li.dataset.t;
    closeList(ed);
    replace(ta, start, ta.selectionStart, term, start + term.length);
    return true;
  }

  // ---- keys --------------------------------------------------------------

  document.addEventListener("keydown", (ev) => {
    const ta = ev.target.closest && ev.target.closest(".ed-in");
    if (!ta) return;
    const ed = ta.closest(".ed"), ul = listOf(ed), open = ul && !ul.hidden;

    if (open && (ev.key === "ArrowDown" || ev.key === "ArrowUp")) {
      const n = ul.children.length, i = +(ul.dataset.i || 0);
      highlight(ul, (i + (ev.key === "ArrowDown" ? 1 : n - 1)) % n);
      return ev.preventDefault();
    }
    if (open && ev.key === "Escape") { closeList(ed); return ev.preventDefault(); }

    if (ev.key === "Tab" && !ev.shiftKey) {
      ev.preventDefault();
      if (accept(ed)) return;
      // re-indent the line the caret is on, and keep the caret where it was in the text
      const start = lineStartOf(ta.value, ta.selectionStart);
      const rest = /^[ \t]*/.exec(ta.value.slice(start))[0];
      const want = " ".repeat(indentAt(ta.value, start));
      const caret = Math.max(start + want.length,
        ta.selectionStart + want.length - rest.length);
      return replace(ta, start, start + rest.length, want, caret);
    }

    if (ev.key === "Enter" && !ev.shiftKey) {
      if (accept(ed)) return ev.preventDefault();
      if (ed.hasAttribute("data-ed-submit")) {
        ev.preventDefault();
        const form = ta.closest("form");
        if (form) form.requestSubmit ? form.requestSubmit() : form.submit();
        return;
      }
      ev.preventDefault();
      const pad = " ".repeat(indentAt(ta.value, ta.selectionStart));
      return replace(ta, ta.selectionStart, ta.selectionEnd, "\n" + pad);
    }
  });

  // ---- repaint -----------------------------------------------------------

  const eds = () => document.querySelectorAll(".ed");

  document.addEventListener("input", (ev) => {
    const ta = ev.target.closest && ev.target.closest(".ed-in");
    if (!ta) return;
    paint(ta.closest(".ed"));
    suggest(ta.closest(".ed"));
  });
  document.addEventListener("scroll", (ev) => {
    const ta = ev.target.closest && ev.target.closest(".ed-in");
    if (ta) paint(ta.closest(".ed"));
  }, true);
  document.addEventListener("click", (ev) => {
    const li = ev.target.closest && ev.target.closest(".ed-complete li");
    if (li) {
      const ed = li.closest(".ed");
      highlight(listOf(ed), Array.prototype.indexOf.call(li.parentNode.children, li));
      accept(ed);
      const ta = ed.querySelector(".ed-in");
      if (ta) ta.focus();
      return;
    }
    // a press anywhere else puts the list away
    eds().forEach((ed) => { if (!ed.contains(ev.target)) closeList(ed); });
  });

  const repaintAll = () => eds().forEach(paint);
  document.addEventListener("htmx:afterSwap", repaintAll);
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", repaintAll);
  else repaintAll();
})();
