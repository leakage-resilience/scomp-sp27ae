from Jasmin require import JWord JWord_array.

require import ArrayWords3W32 ArrayWords12W8.

clone export SubArrayCast as SubArrayDirect3W32_12W8  with op sizeWS <- 4,
                                                           op sizeWB <- 1,
                                                           op sizeS <- 3,
                                                           op sizeB <- 12,
                                                           theory WordS <- W32,
                                                           theory WordB <- W8,
                                                           theory ArrayWordsS <= ArrayWords3W32,
                                                           theory ArrayWordsB <= ArrayWords12W8.
