from Jasmin require import JWord JWord_array.

require import ArrayWords4W8 ArrayWords1W32.

clone export SubArrayCast as SubArrayDirect4W8_1W32  with op sizeWS <- 1,
                                                          op sizeWB <- 4,
                                                          op sizeS <- 4,
                                                          op sizeB <- 1,
                                                          theory WordS <- W8,
                                                          theory WordB <- W32,
                                                          theory ArrayWordsS <= ArrayWords4W8,
                                                          theory ArrayWordsB <= ArrayWords1W32.
