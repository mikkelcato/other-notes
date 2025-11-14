#import "@preview/ctheorems:1.1.3": *

// note template w. terafox
#let note(
  title: none,
  authors: (),
  abstract: [],
  doc,
) = {
  // page
  set page(
    fill: rgb("1e1e1e"),
    numbering: "1",
  )

  // general text
  set text(size: 12pt, fill: rgb("ffffff"))

  v(150pt)
  // title
  set align(center)
  text(size: 24pt, fill: rgb("ffffff"), title)

  // headings
  show heading.where(level: 1): set text(15pt, rgb("#ffffff"))
  show heading.where(level: 2): set text(14pt, rgb("#ffffff"))
  set heading(
    numbering: "1.",
  )

  // authors
  let count = authors.len()
  let ncols = calc.min(count, 3)
  grid(
    columns: (1fr,) * ncols,
    row-gutter: 24pt,
    ..authors.map(author => [
      #author.name
      // #author.affiliation \
      // #link("mailto:" + author.email)
    ]),
  )

  v(10pt)
  // abstract
  par(justify: false)[
    #text(size: 15pt, fill: rgb("ffffff"), [*Abstract*]) \
    #abstract
  ]

  pagebreak()

  show outline.entry.where(
    level: 1,
  ): set block(above: 1em)
  outline()

  pagebreak()
  set align(left)
  doc
}

#set par(
  first-line-indent: 1em,
  spacing: 0.65em,
  justify: true,
)

// def, ex, thm, proof etc.
#let def = thmbox(
  "def",
  "Definition",
  fill: rgb("#1e1c1f"),
  stroke: rgb("#ffffff") + 1pt,
)

#let ex = thmbox("ex", "Example", base_level: 0)

#let thm = thmbox(
  "thm",
  "Theorem",
  base_level: 0,
  fill: rgb("#1e1c1f"),
  stroke: rgb("#ffffff") + 1pt,
)

#let lemma = thmbox(
  "thm",
  "Lemma",
  base_level: 0,
  fill: rgb("#1e1c1f"),
  stroke: rgb("#ffffff") + 1pt,
)

#let corollary = thmbox(
  "corollary",
  "Corollary",
  base_level: 0,
  fill: rgb("#1e1c1f"),
  stroke: rgb("#ffffff") + 1pt,
)

#let proof = thmproof("proof", "Proof")
