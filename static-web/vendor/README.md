# Vendored browser libraries

The dependency graph's renderer ships with every generated site, so a site's pages draw the graph
without loading anything from the network. The files are redistributed unmodified under their
licences, which sit next to them. `vbp`/the generator writes them to `-verso-data/vendor/` and
`Commands/graph.mjs` loads them from there (relative to its own URL); a page can still pass other
URLs through the graph options' `libraries` field.

| Library | Version | File | Licence | Source |
|---|---|---|---|---|
| D3 | 7.9.0 | `d3/d3.min.js` | ISC (`d3/LICENSE`) | npm `d3@7.9.0`, `dist/d3.min.js` |
| d3-graphviz | 5.6.0 | `d3-graphviz/d3-graphviz.min.js` | BSD-3-Clause (`d3-graphviz/LICENSE`) | npm `d3-graphviz@5.6.0`, `build/d3-graphviz.min.js` |

`d3-graphviz.min.js` bundles `@hpcc-js/wasm` (Apache-2.0, `d3-graphviz/LICENSE-hpcc-js-wasm`, from
`@hpcc-js/wasm@2.20.0`), whose WebAssembly module is Graphviz 12.1.0 (EPL-1.0,
`d3-graphviz/LICENSE-graphviz`, from the Graphviz repository at tag `12.1.0`) built with Expat (MIT,
`d3-graphviz/LICENSE-expat`). Graphviz's source code is at <https://gitlab.com/graphviz/graphviz>.

## Integrity

The npm tarballs matched the registry's `dist.integrity`:

* `d3-7.9.0.tgz`: `sha512-e1U46jVP+w7Iut8Jt8ri1YsPOvFpg46k+K8TpCb0P+zjCkjkPnV7WzfDJzMHy1LnA+wj5pLT1wjO901gLXeEhA==`
* `d3-graphviz-5.6.0.tgz`: `sha512-46OOyRv5Ioo9kZBc919FVIYPD/ObtdSZxOK1hv+qwmD7TunpPvvmsI1dSdxhVgH4GragJxFZ31+TQC5aOuXzzw==`

`SHA256SUMS` holds the SHA-256 of each vendored file; they are the same files jsDelivr serves at the
URLs the graph used before (`https://cdn.jsdelivr.net/npm/d3@7.9.0/dist/d3.min.js`,
`https://cdn.jsdelivr.net/npm/d3-graphviz@5.6.0/build/d3-graphviz.min.js`). Check with
`(cd static-web/vendor && shasum -a 256 -c SHA256SUMS)`.

To update: download the new tarballs from the npm registry, check their integrity against
`npm view <pkg>@<version> dist.integrity`, copy the same files, and update this table, the
licences and `SHA256SUMS`.
