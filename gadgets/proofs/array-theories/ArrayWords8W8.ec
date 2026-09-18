from Jasmin require import JWord JWord_array.

require import Array8 WArray8.

clone export ArrayWords as ArrayWords8W8  with op sizeW <- 1, op sizeA <- 8,
                                               theory Word <= W8,
                                               theory ArrayN <= Array8,
                                               theory WArrayN <= WArray8.
