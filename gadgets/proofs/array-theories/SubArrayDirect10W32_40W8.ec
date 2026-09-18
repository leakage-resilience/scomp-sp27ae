from Jasmin require import JWord JWord_array.

require import ArrayWords10W32 ArrayWords40W8.

clone export SubArrayCast as SubArrayDirect10W32_40W8  with op sizeWS <- 4,
                                                            op sizeWB <- 1,
                                                            op sizeS <- 10,
                                                            op sizeB <- 40,
                                                            theory WordS <- W32,
                                                            theory WordB <- W8,
                                                            theory ArrayWordsS <= ArrayWords10W32,
                                                            theory ArrayWordsB <= ArrayWords40W8.
