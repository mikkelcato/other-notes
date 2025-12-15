//**** init-ting
#import "@preview/physica:0.9.7": *
#import "temp.typ": *


#show: thmrules.with(qed-symbol: $square$)
#show: note.with(
  title: [
    *small notes of qft in curved backgrounds.*
  ],
  authors: (
    (
      name: "mkh",
    ),
  ),
  abstract: [
    All errors are likely mine.
  ],
)

= Introduction
_Traditional_ quantum field theory deals with problems of finding cross-sections for transitions between different particle states. These notes treat quantum fields interacting with a strong external field, the _background_. We take this background to be classical. And to make things easier we take the quantum fields to be free meaning they only interact with the background. This strong gravitational coupling leads to many interesting effects.

#include "chpt/chpt-1.typ"
