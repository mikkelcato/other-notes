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
#let pink = "#feacf730"

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
    paper: "us-letter",
    numbering: "1",
  )

  // general text
  set text(
    size: 12pt,
    fill: rgb(black),
    font: "New Computer Modern", // LaTeX font
  )

  show math.equation: set text(font: "New Computer Modern Math")

  v(150pt)
  // title
  set align(center)
  text(size: 24pt, fill: rgb(black), title)

  // headings
  show heading: set block(below: 1.2em)
  show heading.where(level: 1): set text(16pt, rgb(black))
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
  ): set block(above: 1em, below: 0.8em)
  outline(depth: 2)
  set par(
    first-line-indent: 1em,
    spacing: 1.2em,
    leading: 0.65em,
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
  fill: rgb(green),
  stroke: rgb(black) + 0pt,
  padding: (top: 0em, bottom: 0em),
)

#let ex = thmbox(
  "ex",
  "Example",
  base_level: 0,
  padding: (top: 0.0em, bottom: 0.0em),
  breakable: true,
)

#let thm = thmbox(
  "thm",
  "Theorem",
  base_level: 0,
  fill: rgb(red),
  stroke: rgb(black) + 0pt,
  padding: (top: 0.0em, bottom: 0.0em),
)

#let lemma = thmbox(
  "thm",
  "Lemma",
  base_level: 0,
  fill: rgb(yellow),
  stroke: rgb(black) + 0pt,
  padding: (top: 0.0em, bottom: 0.0em),
)

#let proposition = thmbox(
  "prop",
  "Proposition",
  base_level: 0,
  fill: rgb(orange),
  stroke: rgb(black) + 0pt,
  padding: (top: 0.0em, bottom: 0.0em),
)

#let corollary = thmbox(
  "corollary",
  "Corollary",
  base_level: 0,
  fill: rgb(pink),
  stroke: rgb(black) + 0pt,
  padding: (top: 0.0em, bottom: 0.0em),
)

#let proof = thmproof(
  "proof",
  "Proof",
  padding: (top: 0.0em, bottom: 0.0em),
)
