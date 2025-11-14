#import "@preview/physica:0.9.5": *
#import "temp.typ": *


#show: thmrules.with(qed-symbol: $square$)
#show: note.with(
  title: [
    *group theory*
  ],
  authors: (
    (
      name: "mikkelius_",
    ),
  ),
  abstract: [
    notes on group theory, inspired heavily by Dexter Chua's Cambridge notes---essentially just these rewritten in Typst with some stuff added/removed. I have commented out some of the parts that became less relevant to me over time, otherwise these notes would be very bloated---e.g. some alternating group and Möbius group stuff.
  ],
)

= Introduction to Groups
Group theory is what we would call an algebra. An algebra is some structure with operations, defined through a set of axioms. Group theory can be described as the study of symmetries, since the axioms are essentially defined such that symmetries follow them -- or such that sets of symmetries are groups. What rules should this set of symmetries follow? The symmetry of doing nothing is a symmetry, so we should have some identity leaving our object unchanged. Every symmetry should also have a reverse symmetry or inverse, and lastly symmetries should be associative. A group is any set with these properties.

_Note that many parts have been commented out to save space_

#include "chpt/chpt-1.typ"
#include "chpt/chpt-2.typ"
#include "chpt/chpt-3.typ"
