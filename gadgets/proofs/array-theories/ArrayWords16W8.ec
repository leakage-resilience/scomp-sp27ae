from Jasmin require import JWord JWord_array.

require import Array16 WArray16.

clone export ArrayWords as ArrayWords16W8  with op sizeW <- 1,
                                                op sizeA <- 16,
                                                theory Word <= W8,
                                                theory ArrayN <= Array16,
                                                theory WArrayN <= WArray16.
