require import AllCore IntDiv CoreMap List.
require import JModel.

require import Array76.
require import WArray76.



module M = {
  proc rng (range:W64.t) : W64.t = {
    
    var rand_number:W64.t;
    
    rand_number <- RDRAND ;
    rand_number <- (rand_number \umod range);
    return (rand_number);
  }
  
  proc random_char_generator (range:W64.t, set:W8.t Array76.t) : W8.t = {
    
    var char:W8.t;
    var choice_0:W64.t;
    
    choice_0 <@ rng (range);
    char <- set.[(W64.to_uint choice_0)];
    return (char);
  }
  
  proc permutation (p_string:W64.t, string_len:W64.t) : unit = {
    
    var i:W64.t;
    var j:W64.t;
    var aux:W8.t;
    
    i <- string_len;
    
    while (((W64.of_int 0) \ult i)) {
      j <@ rng (i);
      i <- (i - (W64.of_int 1));
      aux <- (loadW8 Glob.mem (W64.to_uint (p_string + i)));
      Glob.mem <-
      storeW8 Glob.mem (W64.to_uint (p_string + i)) (loadW8 Glob.mem (W64.to_uint (p_string + j)));
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (p_string + j)) aux;
    }
    return ();
  }
  
  proc define_union_set (lowercase_available:W64.t,
                         uppercase_available:W64.t, numbers_available:W64.t,
                         special_available:W64.t,
                         lowercase_set:W8.t Array76.t,
                         uppercase_set:W8.t Array76.t,
                         numbers_set:W8.t Array76.t,
                         special_set:W8.t Array76.t, union_set:W8.t Array76.t) : 
  W64.t * W8.t Array76.t = {
    
    var i_set:W64.t;
    var i:W64.t;
    var tmp:W8.t;
    
    i_set <- (W64.of_int 0);
    if ((lowercase_available = (W64.of_int 1))) {
      i <- (W64.of_int 0);
      
      while ((i \ult (W64.of_int 26))) {
        tmp <- lowercase_set.[(W64.to_uint i)];
        union_set.[(W64.to_uint i_set)] <- tmp;
        i <- (i + (W64.of_int 1));
        i_set <- (i_set + (W64.of_int 1));
      }
    } else {
      
    }
    if ((uppercase_available = (W64.of_int 1))) {
      i <- (W64.of_int 0);
      
      while ((i \ult (W64.of_int 26))) {
        tmp <- uppercase_set.[(W64.to_uint i)];
        union_set.[(W64.to_uint i_set)] <- tmp;
        i <- (i + (W64.of_int 1));
        i_set <- (i_set + (W64.of_int 1));
      }
    } else {
      
    }
    if ((numbers_available = (W64.of_int 1))) {
      i <- (W64.of_int 0);
      
      while ((i \ult (W64.of_int 10))) {
        tmp <- numbers_set.[(W64.to_uint i)];
        union_set.[(W64.to_uint i_set)] <- tmp;
        i <- (i + (W64.of_int 1));
        i_set <- (i_set + (W64.of_int 1));
      }
    } else {
      
    }
    if ((special_available = (W64.of_int 1))) {
      i <- (W64.of_int 0);
      
      while ((i \ult (W64.of_int 14))) {
        tmp <- special_set.[(W64.to_uint i)];
        union_set.[(W64.to_uint i_set)] <- tmp;
        i <- (i + (W64.of_int 1));
        i_set <- (i_set + (W64.of_int 1));
      }
    } else {
      
    }
    return (i_set, union_set);
  }
  
  proc generatePassword (length:W64.t, lowercase_policies:W64.t,
                         uppercase_policies:W64.t, numbers_policies:W64.t,
                         special_policies:W64.t, p_output:W64.t) : W64.t = {
    
    var output:W64.t;
    var lowercase_available:W64.t;
    var uppercase_available:W64.t;
    var numbers_available:W64.t;
    var special_available:W64.t;
    var lowercase_min:W64.t;
    var uppercase_min:W64.t;
    var numbers_min:W64.t;
    var special_min:W64.t;
    var lowercase_max:W64.t;
    var uppercase_max:W64.t;
    var numbers_max:W64.t;
    var special_max:W64.t;
    var tmp64_1:W64.t;
    var tmp64_2:W64.t;
    var lowercase_set:W8.t Array76.t;
    var i:W64.t;
    var uppercase_set:W8.t Array76.t;
    var numbers_set:W8.t Array76.t;
    var special_set:W8.t Array76.t;
    var union_set:W8.t Array76.t;
    var i_filled:W64.t;
    var tmp8:W8.t;
    lowercase_set <- witness;
    numbers_set <- witness;
    special_set <- witness;
    union_set <- witness;
    uppercase_set <- witness;
    lowercase_available <-
    (loadW64 Glob.mem (W64.to_uint (lowercase_policies + (W64.of_int 0))));
    uppercase_available <-
    (loadW64 Glob.mem (W64.to_uint (uppercase_policies + (W64.of_int 0))));
    numbers_available <-
    (loadW64 Glob.mem (W64.to_uint (numbers_policies + (W64.of_int 0))));
    special_available <-
    (loadW64 Glob.mem (W64.to_uint (special_policies + (W64.of_int 0))));
    if ((lowercase_available <> (W64.of_int 0))) {
      lowercase_available <- (W64.of_int 1);
    } else {
      
    }
    if ((uppercase_available <> (W64.of_int 0))) {
      uppercase_available <- (W64.of_int 1);
    } else {
      
    }
    if ((numbers_available <> (W64.of_int 0))) {
      numbers_available <- (W64.of_int 1);
    } else {
      
    }
    if ((special_available <> (W64.of_int 0))) {
      special_available <- (W64.of_int 1);
    } else {
      
    }
    lowercase_min <-
    (loadW64 Glob.mem (W64.to_uint (lowercase_policies + (W64.of_int 8))));
    uppercase_min <-
    (loadW64 Glob.mem (W64.to_uint (uppercase_policies + (W64.of_int 8))));
    numbers_min <-
    (loadW64 Glob.mem (W64.to_uint (numbers_policies + (W64.of_int 8))));
    special_min <-
    (loadW64 Glob.mem (W64.to_uint (special_policies + (W64.of_int 8))));
    lowercase_max <-
    (loadW64 Glob.mem (W64.to_uint (lowercase_policies + (W64.of_int 16))));
    uppercase_max <-
    (loadW64 Glob.mem (W64.to_uint (uppercase_policies + (W64.of_int 16))));
    numbers_max <-
    (loadW64 Glob.mem (W64.to_uint (numbers_policies + (W64.of_int 16))));
    special_max <-
    (loadW64 Glob.mem (W64.to_uint (special_policies + (W64.of_int 16))));
    if ((lowercase_max = (W64.of_int 0))) {
      lowercase_max <- (W64.of_int 200);
    } else {
      
    }
    if ((uppercase_max = (W64.of_int 0))) {
      uppercase_max <- (W64.of_int 200);
    } else {
      
    }
    if ((numbers_max = (W64.of_int 0))) {
      numbers_max <- (W64.of_int 200);
    } else {
      
    }
    if ((special_max = (W64.of_int 0))) {
      special_max <- (W64.of_int 200);
    } else {
      
    }
    if ((length \sle (W64.of_int 200))) {
      if (((W64.of_int 0) \sle length)) {
        tmp64_1 <- lowercase_available;
        tmp64_2 <- uppercase_available;
        tmp64_1 <- (tmp64_1 + tmp64_2);
        tmp64_2 <- numbers_available;
        tmp64_1 <- (tmp64_1 + tmp64_2);
        tmp64_2 <- special_available;
        tmp64_1 <- (tmp64_1 + special_available);
        if (((W64.of_int 0) \ult tmp64_1)) {
          tmp64_1 <- lowercase_min;
          if (((W64.of_int 0) \sle tmp64_1)) {
            tmp64_1 <- uppercase_min;
            if (((W64.of_int 0) \sle tmp64_1)) {
              tmp64_1 <- numbers_min;
              if (((W64.of_int 0) \sle tmp64_1)) {
                tmp64_1 <- special_min;
                if (((W64.of_int 0) \sle tmp64_1)) {
                  tmp64_1 <- lowercase_max;
                  if (((W64.of_int 0) \sle tmp64_1)) {
                    tmp64_1 <- uppercase_max;
                    if (((W64.of_int 0) \sle tmp64_1)) {
                      tmp64_1 <- numbers_max;
                      if (((W64.of_int 0) \sle tmp64_1)) {
                        tmp64_1 <- special_max;
                        if (((W64.of_int 0) \sle tmp64_1)) {
                          tmp64_1 <- lowercase_max;
                          tmp64_2 <- lowercase_min;
                          if ((tmp64_2 \ule tmp64_1)) {
                            tmp64_1 <- uppercase_max;
                            tmp64_2 <- uppercase_min;
                            if ((tmp64_2 \ule tmp64_1)) {
                              tmp64_1 <- numbers_max;
                              tmp64_2 <- numbers_min;
                              if ((tmp64_2 \ule tmp64_1)) {
                                tmp64_1 <- special_max;
                                tmp64_2 <- special_min;
                                if ((tmp64_2 \ule tmp64_1)) {
                                  tmp64_1 <- lowercase_min;
                                  tmp64_2 <- uppercase_min;
                                  tmp64_1 <- (tmp64_1 + tmp64_2);
                                  tmp64_2 <- numbers_min;
                                  tmp64_1 <- (tmp64_1 + tmp64_2);
                                  tmp64_2 <- special_min;
                                  tmp64_1 <- (tmp64_1 + tmp64_2);
                                  if ((tmp64_1 \ule length)) {
                                    tmp64_1 <- (W64.of_int 0);
                                    if ((lowercase_available = (W64.of_int 1))) {
                                      tmp64_2 <- lowercase_max;
                                      tmp64_1 <- (tmp64_1 + tmp64_2);
                                    } else {
                                      
                                    }
                                    if ((uppercase_available = (W64.of_int 1))) {
                                      tmp64_2 <- uppercase_max;
                                      tmp64_1 <- (tmp64_1 + tmp64_2);
                                    } else {
                                      
                                    }
                                    if ((numbers_available = (W64.of_int 1))) {
                                      tmp64_2 <- numbers_max;
                                      tmp64_1 <- (tmp64_1 + tmp64_2);
                                    } else {
                                      
                                    }
                                    if ((special_available = (W64.of_int 1))) {
                                      tmp64_2 <- lowercase_max;
                                      tmp64_1 <- (tmp64_1 + tmp64_2);
                                    } else {
                                      
                                    }
                                    if ((length \ule tmp64_1)) {
                                      lowercase_set.[0] <- (W8.of_int 97);
                                      lowercase_set.[1] <- (W8.of_int 98);
                                      lowercase_set.[2] <- (W8.of_int 99);
                                      lowercase_set.[3] <- (W8.of_int 100);
                                      lowercase_set.[4] <- (W8.of_int 101);
                                      lowercase_set.[5] <- (W8.of_int 102);
                                      lowercase_set.[6] <- (W8.of_int 103);
                                      lowercase_set.[7] <- (W8.of_int 104);
                                      lowercase_set.[8] <- (W8.of_int 105);
                                      lowercase_set.[9] <- (W8.of_int 106);
                                      lowercase_set.[10] <- (W8.of_int 107);
                                      lowercase_set.[11] <- (W8.of_int 108);
                                      lowercase_set.[12] <- (W8.of_int 109);
                                      lowercase_set.[13] <- (W8.of_int 110);
                                      lowercase_set.[14] <- (W8.of_int 111);
                                      lowercase_set.[15] <- (W8.of_int 112);
                                      lowercase_set.[16] <- (W8.of_int 113);
                                      lowercase_set.[17] <- (W8.of_int 114);
                                      lowercase_set.[18] <- (W8.of_int 115);
                                      lowercase_set.[19] <- (W8.of_int 116);
                                      lowercase_set.[20] <- (W8.of_int 117);
                                      lowercase_set.[21] <- (W8.of_int 118);
                                      lowercase_set.[22] <- (W8.of_int 119);
                                      lowercase_set.[23] <- (W8.of_int 120);
                                      lowercase_set.[24] <- (W8.of_int 121);
                                      lowercase_set.[25] <- (W8.of_int 122);
                                      i <- (W64.of_int 26);
                                      
                                      while ((i \ult (W64.of_int 76))) {
                                        lowercase_set.[(W64.to_uint i)] <-
                                        (W8.of_int 0);
                                        i <- (i + (W64.of_int 1));
                                      }
                                      uppercase_set.[0] <- (W8.of_int 65);
                                      uppercase_set.[1] <- (W8.of_int 66);
                                      uppercase_set.[2] <- (W8.of_int 67);
                                      uppercase_set.[3] <- (W8.of_int 68);
                                      uppercase_set.[4] <- (W8.of_int 69);
                                      uppercase_set.[5] <- (W8.of_int 70);
                                      uppercase_set.[6] <- (W8.of_int 71);
                                      uppercase_set.[7] <- (W8.of_int 72);
                                      uppercase_set.[8] <- (W8.of_int 73);
                                      uppercase_set.[9] <- (W8.of_int 74);
                                      uppercase_set.[10] <- (W8.of_int 75);
                                      uppercase_set.[11] <- (W8.of_int 76);
                                      uppercase_set.[12] <- (W8.of_int 77);
                                      uppercase_set.[13] <- (W8.of_int 78);
                                      uppercase_set.[14] <- (W8.of_int 79);
                                      uppercase_set.[15] <- (W8.of_int 80);
                                      uppercase_set.[16] <- (W8.of_int 81);
                                      uppercase_set.[17] <- (W8.of_int 82);
                                      uppercase_set.[18] <- (W8.of_int 83);
                                      uppercase_set.[19] <- (W8.of_int 84);
                                      uppercase_set.[20] <- (W8.of_int 85);
                                      uppercase_set.[21] <- (W8.of_int 86);
                                      uppercase_set.[22] <- (W8.of_int 87);
                                      uppercase_set.[23] <- (W8.of_int 88);
                                      uppercase_set.[24] <- (W8.of_int 89);
                                      uppercase_set.[25] <- (W8.of_int 90);
                                      i <- (W64.of_int 26);
                                      
                                      while ((i \ult (W64.of_int 76))) {
                                        uppercase_set.[(W64.to_uint i)] <-
                                        (W8.of_int 0);
                                        i <- (i + (W64.of_int 1));
                                      }
                                      numbers_set.[0] <- (W8.of_int 48);
                                      numbers_set.[1] <- (W8.of_int 49);
                                      numbers_set.[2] <- (W8.of_int 50);
                                      numbers_set.[3] <- (W8.of_int 51);
                                      numbers_set.[4] <- (W8.of_int 52);
                                      numbers_set.[5] <- (W8.of_int 53);
                                      numbers_set.[6] <- (W8.of_int 54);
                                      numbers_set.[7] <- (W8.of_int 55);
                                      numbers_set.[8] <- (W8.of_int 56);
                                      numbers_set.[9] <- (W8.of_int 57);
                                      i <- (W64.of_int 10);
                                      
                                      while ((i \ult (W64.of_int 76))) {
                                        numbers_set.[(W64.to_uint i)] <-
                                        (W8.of_int 0);
                                        i <- (i + (W64.of_int 1));
                                      }
                                      special_set.[0] <- (W8.of_int 33);
                                      special_set.[1] <- (W8.of_int 63);
                                      special_set.[2] <- (W8.of_int 35);
                                      special_set.[3] <- (W8.of_int 36);
                                      special_set.[4] <- (W8.of_int 37);
                                      special_set.[5] <- (W8.of_int 38);
                                      special_set.[6] <- (W8.of_int 43);
                                      special_set.[7] <- (W8.of_int 45);
                                      special_set.[8] <- (W8.of_int 42);
                                      special_set.[9] <- (W8.of_int 95);
                                      special_set.[10] <- (W8.of_int 64);
                                      special_set.[11] <- (W8.of_int 58);
                                      special_set.[12] <- (W8.of_int 59);
                                      special_set.[13] <- (W8.of_int 61);
                                      i <- (W64.of_int 14);
                                      
                                      while ((i \ult (W64.of_int 76))) {
                                        special_set.[(W64.to_uint i)] <-
                                        (W8.of_int 0);
                                        i <- (i + (W64.of_int 1));
                                      }
                                      i <- (W64.of_int 0);
                                      
                                      while ((i \ult (W64.of_int 76))) {
                                        union_set.[(W64.to_uint i)] <-
                                        (W8.of_int 0);
                                        i <- (i + (W64.of_int 1));
                                      }
                                      i_filled <- (W64.of_int 0);
                                      if ((lowercase_available = (W64.of_int 1))) {
                                        i <- (W64.of_int 0);
                                        
                                        while ((i \ult lowercase_min)) {
                                          lowercase_max <-
                                          (lowercase_max - (W64.of_int 1));
                                          if ((lowercase_max = (W64.of_int 0))) {
                                            lowercase_available <-
                                            (W64.of_int 0);
                                          } else {
                                            
                                          }
                                          tmp8 <@ random_char_generator ((W64.of_int 26),
                                          lowercase_set);
                                          Glob.mem <-
                                          storeW8 Glob.mem (W64.to_uint (p_output + i_filled)) tmp8;
                                          i <- (i + (W64.of_int 1));
                                          i_filled <-
                                          (i_filled + (W64.of_int 1));
                                        }
                                      } else {
                                        
                                      }
                                      if ((uppercase_available = (W64.of_int 1))) {
                                        i <- (W64.of_int 0);
                                        
                                        while ((i \ult uppercase_min)) {
                                          uppercase_max <-
                                          (uppercase_max - (W64.of_int 1));
                                          if ((uppercase_max = (W64.of_int 0))) {
                                            uppercase_available <-
                                            (W64.of_int 0);
                                          } else {
                                            
                                          }
                                          tmp8 <@ random_char_generator ((W64.of_int 26),
                                          uppercase_set);
                                          Glob.mem <-
                                          storeW8 Glob.mem (W64.to_uint (p_output + i_filled)) tmp8;
                                          i <- (i + (W64.of_int 1));
                                          i_filled <-
                                          (i_filled + (W64.of_int 1));
                                        }
                                      } else {
                                        
                                      }
                                      if ((numbers_available = (W64.of_int 1))) {
                                        i <- (W64.of_int 0);
                                        
                                        while ((i \ult numbers_min)) {
                                          numbers_max <-
                                          (numbers_max - (W64.of_int 1));
                                          if ((numbers_max = (W64.of_int 0))) {
                                            numbers_available <-
                                            (W64.of_int 0);
                                          } else {
                                            
                                          }
                                          tmp8 <@ random_char_generator ((W64.of_int 10),
                                          numbers_set);
                                          Glob.mem <-
                                          storeW8 Glob.mem (W64.to_uint (p_output + i_filled)) tmp8;
                                          i <- (i + (W64.of_int 1));
                                          i_filled <-
                                          (i_filled + (W64.of_int 1));
                                        }
                                      } else {
                                        
                                      }
                                      if ((special_available = (W64.of_int 1))) {
                                        i <- (W64.of_int 0);
                                        
                                        while ((i \ult special_min)) {
                                          special_max <-
                                          (special_max - (W64.of_int 1));
                                          if ((special_max = (W64.of_int 0))) {
                                            special_available <-
                                            (W64.of_int 0);
                                          } else {
                                            
                                          }
                                          tmp8 <@ random_char_generator ((W64.of_int 14),
                                          special_set);
                                          Glob.mem <-
                                          storeW8 Glob.mem (W64.to_uint (p_output + i_filled)) tmp8;
                                          i <- (i + (W64.of_int 1));
                                          i_filled <-
                                          (i_filled + (W64.of_int 1));
                                        }
                                      } else {
                                        
                                      }
                                      (tmp64_1,
                                      union_set) <@ define_union_set (lowercase_available,
                                      uppercase_available, numbers_available,
                                      special_available, lowercase_set,
                                      uppercase_set, numbers_set,
                                      special_set, union_set);
                                      
                                      while ((i_filled \ult length)) {
                                        tmp8 <@ random_char_generator (tmp64_1,
                                        union_set);
                                        if (((W8.of_int 97) \ule tmp8)) {
                                          if ((tmp8 \ule (W8.of_int 122))) {
                                            lowercase_max <-
                                            (lowercase_max - (W64.of_int 1));
                                            if ((lowercase_max = (W64.of_int 0))) {
                                              lowercase_available <-
                                              (W64.of_int 0);
                                              (tmp64_1,
                                              union_set) <@ define_union_set (lowercase_available,
                                              uppercase_available,
                                              numbers_available,
                                              special_available,
                                              lowercase_set, uppercase_set,
                                              numbers_set, special_set,
                                              union_set);
                                            } else {
                                              
                                            }
                                          } else {
                                            
                                          }
                                        } else {
                                          if (((W8.of_int 65) \ule tmp8)) {
                                            if ((tmp8 \ule (W8.of_int 90))) {
                                              uppercase_max <-
                                              (uppercase_max - (W64.of_int 1));
                                              if ((uppercase_max = (W64.of_int 0))) {
                                                uppercase_available <-
                                                (W64.of_int 0);
                                                (tmp64_1,
                                                union_set) <@ define_union_set (lowercase_available,
                                                uppercase_available,
                                                numbers_available,
                                                special_available,
                                                lowercase_set, uppercase_set,
                                                numbers_set, special_set,
                                                union_set);
                                              } else {
                                                
                                              }
                                            } else {
                                              
                                            }
                                          } else {
                                            if (((W8.of_int 48) \ule tmp8)) {
                                              if ((tmp8 \ule (W8.of_int 57))) {
                                                numbers_max <-
                                                (numbers_max - (W64.of_int 1));
                                                if ((numbers_max = (W64.of_int 0))) {
                                                  numbers_available <-
                                                  (W64.of_int 0);
                                                  (tmp64_1,
                                                  union_set) <@ define_union_set (lowercase_available,
                                                  uppercase_available,
                                                  numbers_available,
                                                  special_available,
                                                  lowercase_set,
                                                  uppercase_set, numbers_set,
                                                  special_set, union_set);
                                                } else {
                                                  
                                                }
                                              } else {
                                                
                                              }
                                            } else {
                                              special_max <-
                                              (special_max - (W64.of_int 1));
                                              if ((special_max = (W64.of_int 0))) {
                                                special_available <-
                                                (W64.of_int 0);
                                                (tmp64_1,
                                                union_set) <@ define_union_set (lowercase_available,
                                                uppercase_available,
                                                numbers_available,
                                                special_available,
                                                lowercase_set, uppercase_set,
                                                numbers_set, special_set,
                                                union_set);
                                              } else {
                                                
                                              }
                                            }
                                          }
                                        }
                                        Glob.mem <-
                                        storeW8 Glob.mem (W64.to_uint (p_output + i_filled)) tmp8;
                                        i_filled <-
                                        (i_filled + (W64.of_int 1));
                                      }
                                      permutation (p_output, length);
                                      Glob.mem <-
                                      storeW64 Glob.mem (W64.to_uint (p_output + length)) (W64.of_int 0);
                                      output <- (W64.of_int 1);
                                    } else {
                                      output <- (W64.of_int (- 17));
                                    }
                                  } else {
                                    output <- (W64.of_int (- 16));
                                  }
                                } else {
                                  output <- (W64.of_int (- 15));
                                }
                              } else {
                                output <- (W64.of_int (- 14));
                              }
                            } else {
                              output <- (W64.of_int (- 13));
                            }
                          } else {
                            output <- (W64.of_int (- 12));
                          }
                        } else {
                          output <- (W64.of_int (- 11));
                        }
                      } else {
                        output <- (W64.of_int (- 10));
                      }
                    } else {
                      output <- (W64.of_int (- 9));
                    }
                  } else {
                    output <- (W64.of_int (- 8));
                  }
                } else {
                  output <- (W64.of_int (- 7));
                }
              } else {
                output <- (W64.of_int (- 6));
              }
            } else {
              output <- (W64.of_int (- 5));
            }
          } else {
            output <- (W64.of_int (- 4));
          }
        } else {
          output <- (W64.of_int (- 3));
        }
      } else {
        output <- (W64.of_int (- 2));
      }
    } else {
      output <- (W64.of_int (- 1));
    }
    return (output);
  }
}.

