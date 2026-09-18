from Jasmin require import JWord JWord_array.

require import ArrayWords40W8 ArrayWords10W32.

clone export SubArrayCast as SubArrayDirect40W8_10W32  with op sizeWS <- 1,
                                                            op sizeWB <- 4,
                                                            op sizeS <- 40,
                                                            op sizeB <- 10,
                                                            theory WordS <- W8,
                                                            theory WordB <- W32,
                                                            theory ArrayWordsS <= ArrayWords40W8,
                                                            theory ArrayWordsB <= ArrayWords10W32.
