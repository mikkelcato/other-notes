#import "@preview/ctheorems:1.1.3": *
#import "@preview/equate:0.3.2": equate

#let white = "#ffffff"
#let black = "#000000"
#let grey = "#1e1e1e"
#let green = "#88fd9f30"
#let yellow = "#faffb055"
#let orange = "#ffccb340"
#let blue = "#acc4ff30"
#let red = "#ffa9bd30"

// note template
#let note(
  title: none,
  authors: (),
  abstract: [],
  doc,
) = {
  // page
  set page(
    fill: rgb(white),
    numbering: "1",
  )

  // general text
  set text(size: 12pt, fill: rgb(black))

  v(150pt)
  // title
  set align(center)
  text(size: 24pt, fill: rgb(black), title)

  // headings
  show heading.where(level: 1): set text(15pt, rgb(black))
  show heading.where(level: 2): set text(14pt, rgb(black))
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
    #text(size: 15pt, fill: rgb(black), [*Abstract*]) \
    #abstract
  ]

  pagebreak()

  show outline.entry.where(
    level: 1,
  ): set block(above: 1em)
  outline()
  set par(
    first-line-indent: 1em,
    spacing: 1.0em,
    justify: true,
  )
  show: equate.with(
    breakable: true,
    sub-numbering: true,
    number-mode: "label",
  )
  set math.equation(
    numbering: "(1.1)",
    //number-align: bottom,
  )

  pagebreak()
  set align(left)
  doc
}

// def, ex, thm, proof etc.
#let def = thmbox(
  "def",
  "Definition",
  fill: rgb(blue),
  stroke: rgb(black) + 0pt,
)

#let ex = thmbox("ex", "Example", base_level: 0)

#let thm = thmbox(
  "thm",
  "Theorem",
  base_level: 0,
  fill: rgb(green),
  stroke: rgb(black) + 0pt,
)

#let lemma = thmbox(
  "thm",
  "Lemma",
  base_level: 0,
  fill: rgb(orange),
  stroke: rgb(black) + 0pt,
)

#let corollary = thmbox(
  "corollary",
  "Corollary",
  base_level: 0,
  fill: rgb(red),
  stroke: rgb(black) + 0pt,
)

#let proof = thmproof("proof", "Proof")
