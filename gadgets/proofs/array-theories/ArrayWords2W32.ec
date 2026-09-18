from Jasmin require import JWord JWord_array.

require import Array2 WArray8.

clone export ArrayWords as ArrayWords2W32  with op sizeW <- 4, op sizeA <- 2,
                                                theory Word <= W32,
                                                theory ArrayN <= Array2,
                                                theory WArrayN <= WArray8.
