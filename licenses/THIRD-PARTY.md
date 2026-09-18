# Third-party assets

Vaelii itself is licensed under the [SSPL-1.0](https://www.mongodb.com/licensing/server-side-public-license)
(see `project.clj`). This file covers the assets **vendored into the repo** — files
checked in under `resources/public/` and served verbatim by the browser
(`vaelii.browser.web`), each under its own upstream licence.

Everything else under `resources/public/` is the project's own work and carries no
third-party obligation: `vaelii.css`, `vaelii.js`, and the marks below. The badge SVGs
under `.github/badges/` are likewise rendered locally by `scripts/update-badges.sh` —
no network, no vendored code — in the visual style of shields.io, which is CC0-1.0.

Runtime Java/Clojure dependencies are *not* here: they are declared in `project.clj`,
resolved by Leiningen, and never copied into this tree. They are inventoried
separately, in [`DEPENDENCIES.md`](DEPENDENCIES.md) — a published coordinate is a
promise about a whole classpath, so the two lists answer different questions and
neither subsumes the other.

Everything below is self-hosted deliberately. A page that loads a script or a font
from a CDN gives that CDN the ability to change what runs in the operator's browser
and a record of every page the operator opens; a vendored copy is a fixed, auditable
artefact instead. The cost is that updates are manual — which is the point, so each
one is a reviewed commit.

## htmx 2.0.9

| | |
|---|---|
| File | `resources/public/htmx.min.js` |
| Licence | 0BSD (Zero-Clause BSD) |
| Upstream | <https://htmx.org> · <https://github.com/bigskysoftware/htmx> |
| Copyright | © 2020 Big Sky Software |

The browser's declarative interactivity: boosted navigation, the header's active
search, and the editor's load/save (docs/web.md).

**To update:** take `dist/htmx.min.js` from the release you want (2.x — the 4.x line
is not stable), keep the `/*! htmx <version> | … */` banner as the file's first line
with the version bumped, and bump the version in this section.

```
Permission to use, copy, modify, and/or distribute this software for any purpose
with or without fee is hereby granted.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND
FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT,
OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE,
DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS
ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS
SOFTWARE.
```

## Atkinson Hyperlegible Next

| | |
|---|---|
| File | `resources/public/font/AtkinsonHyperlegibleNext-Regular.woff2` |
| Licence | SIL Open Font License 1.1 — full text in `resources/public/font/license/AtkinsonHyperlegibleNext-Regular-License.pdf` (Braille Institute ships OFL 1.1 verbatim under an "End-User License Agreement" cover; it adds no clauses) |
| Upstream | <https://www.brailleinstitute.org/freefont/> |
| Copyright | © 2020, 2024 Braille Institute of America, Inc. (<https://www.brailleinstitute.org/freefont/>) |

The proportional face, used for English written for a reader — a paragraph, a hint, a
`comment` string off the KB. A typeface drawn for legibility at a glance, which is what a
page of unfamiliar vocabulary needs.

## Hasklig

| | |
|---|---|
| File | `resources/public/font/Hasklig-Regular.woff2` |
| Licence | SIL Open Font License 1.1 — full text in `resources/public/font/license/Hasklig-License.md` |
| Upstream | <https://github.com/i-tu/Hasklig> (Ian Tuomi) |
| Copyright | © 2010–2019 Adobe (<http://www.adobe.com/>), with Reserved Font Name 'Source' |

The monospace face, used for every piece of formal content — sentences, terms,
handles, index keys, query inputs. Hasklig is Adobe's Source Code Pro with
programming ligatures added.

Only the regular cut of each family is vendored; the browser synthesizes the heavier
weights (`resources/public/vaelii.css`).

## Marks and icons

`logo.svg`, `favicon.svg`, `favicon.ico`, and `apple-touch-icon.png` are vaelii's own
and carry the project's licence.
