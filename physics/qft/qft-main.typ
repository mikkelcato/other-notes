//**** init-ting
#import "@preview/physica:0.9.5": *
#import "temp.typ": *


#show: thmrules.with(qed-symbol: $square$)
#show: note.with(
  title: [
    *introductory quantum field theory*
  ],
  authors: (
    (
      name: "mkh",
    ),
  ),
  abstract: [
    self-study notes of qft.
  ],
)

= Introduction
Quantum field theory is essentially the formalism required to combine quantum mechanics and relativity---we work in natural units: $hbar = c = 1$. These notes are heavily inspired by Timo Weigand's notes.



#include "chpt/chpt-1.typ" // classical field theory
#include "chpt/chpt-2.typ" // free scalar field, spin 0
#include "chpt/chpt-3.typ" // interacting scalar theory
//#include "chpt/chpt-4.typ" // dirac field, spin 1/2
//#include "chpt/chpt-5.typ" // spin 1
