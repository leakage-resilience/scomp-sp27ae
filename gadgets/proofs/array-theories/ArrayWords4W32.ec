from Jasmin require import JWord JWord_array.

require import Array4 WArray16.

clone export ArrayWords as ArrayWords4W32  with op sizeW <- 4, op sizeA <- 4,
                                                theory Word <= W32,
                                                theory ArrayN <= Array4,
                                                theory WArrayN <= WArray16.
