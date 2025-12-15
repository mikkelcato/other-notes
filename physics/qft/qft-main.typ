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
    Notes on introductory quantum field theory. All errors are likely mine.
  ],
)

= Introduction
The first part of these notes are concerned with canonical quantization (Klein-Gordon and Dirac field), and essentially follow the first part of _Peskin and Schroeder_.

The second part of these notes are concerned with introducing path integrals.

We work in natural units $hbar = c = 1$ but notation is likely inconsistent.

#include "chpt/chpt-1.typ" // field theory
#include "chpt/chpt-2.typ" // free scalar field
#include "chpt/chpt-3.typ" // dirac field
#include "chpt/chpt-4.typ" // interacting fields
//#include "chpt/chpt-5.typ" // kählen LSZ
//#include "chpt/chpt-6.typ" // spin 1 (?)
//#include "chpt/chpt-7.typ" // basic path-integrals
