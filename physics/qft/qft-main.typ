//**** init-ting
#import "@preview/physica:0.9.5": *
#import "temp.typ": *


#show: thmrules.with(qed-symbol: $square$)
#show: note.with(
  title: [
    *quantum field theory*
  ],
  authors: (
    (
      name: "mkh",
    ),
  ),
  abstract: [
    self-study notes of qft---currently working through Tong's notes.
  ],
)

= Introduction
The first part of these notes is concerned with canonical quantization (primarily based on Tong's notes)---the second part handles the path integral approach. We'll work with natural units $c = hbar = 1$.

Quantum field theory is essentially the formalism required to combine quantum mechanics and relativity.

#include "chpt/chpt-1.typ"
#include "chpt/chpt-2.typ"
