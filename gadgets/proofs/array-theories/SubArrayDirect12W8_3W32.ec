from Jasmin require import JWord JWord_array.

require import ArrayWords12W8 ArrayWords3W32.

clone export SubArrayCast as SubArrayDirect12W8_3W32  with op sizeWS <- 1,
                                                           op sizeWB <- 4,
                                                           op sizeS <- 12,
                                                           op sizeB <- 3,
                                                           theory WordS <- W8,
                                                           theory WordB <- W32,
                                                           theory ArrayWordsS <= ArrayWords12W8,
                                                           theory ArrayWordsB <= ArrayWords3W32.
