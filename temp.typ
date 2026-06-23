#import "@preview/equate:0.3.2": equate
#import "@preview/physica:0.9.8": *
#import "@preview/fletcher:0.5.8" as fletcher: cetz, diagram, edge, node

#import "@preview/inknertia:0.1.0": feynman
#import "@preview/lemmify:0.1.8": *

#let (
  theorem,
  lemma,
  corollary,
  remark,
  proposition,
  example,
  proof,
  rules: thm-rules,
) = default-theorems("thm-group", lang: "en")

/*
template for main (with title page)
*/

#let note(
  title: none,
  name: [],
  prof: [],
  body,
) = {
  // page
  set page(
    fill: white,
    paper: "a4",
  )

  // general text
  set text(
    size: 12pt,
    fill: black,
    font: "New Computer Modern", // LaTeX font
  )

  v(150pt)
  // title
  set align(center)
  text(size: 24pt, fill: black, title)

  v(15pt)

  par(justify: false)[
    #text(size: 12pt, [by #name])
  ]

  v(50pt)
  // abstract
  par(justify: false)[
    #text(
      size: 12pt,
      [*all errors are mine*],
    )
  ]

  pagebreak()

  set page(numbering: "1")

  // par
  set par(
    first-line-indent: 1.5em,
    leading: 1.5em,
    justify: true,
  )

  // headings
  set heading(
    numbering: "1.",
  )
  show heading: set block(below: 1.2em)
  show heading.where(level: 1): set text(18pt, black)
  show heading.where(level: 2): set text(14pt, black)

  show heading.where(level: 1): it => {
    counter(math.equation).update(0)
    it
  }

  set heading(
    numbering: (..x) => {
      let nums = x.pos()
      nums.at(0) = nums.at(0) - 1
      numbering("1.", ..nums)
    },
  )

  // outline
  show outline.entry.where(
    level: 1,
  ): set block(above: 1.5em)
  show outline.entry.where(
    level: 2,
  ): set block(above: 1.25em)
  outline(depth: 2)

  // figures
  set scale(reflow: true)
  show figure.caption: set text(size: 11pt, style: "italic")
  show figure: set block(spacing: 2em)
  show ref.where(form: "normal"): set ref(supplement: it => {
    if it.func() == figure {
      "Figure"
    }
  })

  // enum
  set enum(
    indent: 1.5em,
    body-indent: 0.75em,
  )

  // equations
  show math.equation: set text(font: "New Computer Modern Math")

  set math.equation(
    numbering: (..nums) => {
      let chapter = counter(heading.where(level: 1)).get().first() - 1
      numbering("(1.1)", chapter, nums.pos().first())
    },
  )

  show: equate.with(
    breakable: true,
    sub-numbering: false,
    number-mode: "label",
  )

  pagebreak()
  set align(left)

  show: thm-rules
  body
}

/*
template for lecture notes
*/

#let lect-note(
  title: none,
  name: [],
  prof: [],
  body,
) = {
  // page
  set page(
    fill: white,
    paper: "a4",
  )

  // general text
  set text(
    size: 12pt,
    fill: black,
    font: "New Computer Modern", // LaTeX font
  )

  v(150pt)
  // title
  set align(center)
  text(size: 24pt, fill: black, title)

  v(15pt)

  par(justify: false)[
    #text(size: 14pt, [Based on lectures by #prof])
  ]

  par(justify: false)[
    #text(size: 10pt, [Notes taken by #name])
  ]

  v(50pt)
  // abstract
  par(justify: false)[
    #text(
      size: 12pt,
      [These notes are not endorsed by the lecturers. All errors are mine.],
    )
  ]

  pagebreak()

  set page(numbering: "1")

  // par
  set par(
    first-line-indent: 1.5em,
    leading: 1.5em,
    justify: true,
  )

  // headings
  set heading(
    numbering: "1.",
  )
  show heading: set block(below: 1.2em)
  show heading.where(level: 1): set text(18pt, black)
  show heading.where(level: 2): set text(14pt, black)

  show heading.where(level: 1): it => {
    counter(math.equation).update(0)
    it
  }

  set heading(
    numbering: (..x) => {
      let nums = x.pos()
      nums.at(0) = nums.at(0) - 1
      numbering("1.", ..nums)
    },
  )

  // outline
  show outline.entry.where(
    level: 1,
  ): set block(above: 1.5em)
  show outline.entry.where(
    level: 2,
  ): set block(above: 1.25em)
  outline(depth: 2)

  // figures
  set scale(reflow: true)
  show figure.caption: set text(size: 11pt, style: "italic")
  show figure: set block(spacing: 2em)
  show ref.where(form: "normal"): set ref(supplement: it => {
    if it.func() == figure {
      "Figure"
    }
  })

  // enum
  set enum(
    indent: 1.5em,
    body-indent: 0.75em,
  )

  // equations
  show math.equation: set text(font: "New Computer Modern Math")

  set math.equation(
    numbering: (..nums) => {
      let chapter = counter(heading.where(level: 1)).get().first() - 1
      numbering("(1.1)", chapter, nums.pos().first())
    },
  )

  show: equate.with(
    breakable: true,
    sub-numbering: false,
    number-mode: "label",
  )

  pagebreak()
  set align(left)

  show: thm-rules
  body
}




/*
template for chapters (no title page, no outline, etc.)
*/

#let chpt-note(body) = {
  // page
  set page(
    fill: white,
    paper: "a4",
    numbering: "1",
  )

  // text and par
  set text(
    size: 12pt,
    fill: black,
    font: "New Computer Modern", // LaTeX font
  )

  set par(
    first-line-indent: 1.5em,
    leading: 1.5em,
    justify: true,
  )

  // headings
  set heading(
    numbering: (..x) => {
      let nums = x.pos()
      nums.at(0) = nums.at(0) - 1
      numbering("1.", ..nums)
    },
  )

  show heading: set block(below: 1.2em)
  show heading.where(level: 1): set text(18pt, black)
  show heading.where(level: 2): set text(14pt, black)

  show heading.where(level: 1): it => {
    counter(math.equation).update(0)
    it
  }

  // figures
  set scale(reflow: true)
  show figure.caption: set text(size: 11pt, style: "italic")
  show figure: set block(spacing: 2em)
  show ref.where(form: "normal"): set ref(supplement: it => {
    if it.func() == figure {
      "Figure"
    }
  })

  // enums
  set enum(
    indent: 1.5em,
    body-indent: 0.75em,
  )

  // equations
  show math.equation: set text(font: "New Computer Modern Math")
  set math.equation(
    numbering: (..nums) => {
      let chapter = counter(heading.where(level: 1)).get().first() - 1
      numbering("(1.1)", chapter, nums.pos().first())
    },
  )
  show: equate.with(
    breakable: true,
    sub-numbering: false,
    number-mode: "label",
  )

  set align(left)

  show: thm-rules

  body
}
