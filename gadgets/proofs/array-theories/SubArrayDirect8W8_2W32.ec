from Jasmin require import JWord JWord_array.

require import ArrayWords8W8 ArrayWords2W32.

clone export SubArrayCast as SubArrayDirect8W8_2W32  with op sizeWS <- 1,
                                                          op sizeWB <- 4,
                                                          op sizeS <- 8,
                                                          op sizeB <- 2,
                                                          theory WordS <- W8,
                                                          theory WordB <- W32,
                                                          theory ArrayWordsS <= ArrayWords8W8,
                                                          theory ArrayWordsB <= ArrayWords2W32.
