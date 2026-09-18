from Jasmin require import JWord JWord_array.

require import ArrayWords2W32 ArrayWords8W8.

clone export SubArrayCast as SubArrayDirect2W32_8W8  with op sizeWS <- 4,
                                                          op sizeWB <- 1,
                                                          op sizeS <- 2,
                                                          op sizeB <- 8,
                                                          theory WordS <- W32,
                                                          theory WordB <- W8,
                                                          theory ArrayWordsS <= ArrayWords2W32,
                                                          theory ArrayWordsB <= ArrayWords8W8.
