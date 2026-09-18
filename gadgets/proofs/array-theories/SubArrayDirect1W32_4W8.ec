from Jasmin require import JWord JWord_array.

require import ArrayWords1W32 ArrayWords4W8.

clone export SubArrayCast as SubArrayDirect1W32_4W8  with op sizeWS <- 4,
                                                          op sizeWB <- 1,
                                                          op sizeS <- 1,
                                                          op sizeB <- 4,
                                                          theory WordS <- W32,
                                                          theory WordB <- W8,
                                                          theory ArrayWordsS <= ArrayWords1W32,
                                                          theory ArrayWordsB <= ArrayWords4W8.
