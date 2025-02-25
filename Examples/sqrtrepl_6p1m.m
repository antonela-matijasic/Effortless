(* Created with the Wolfram Language : www.wolfram.com *)
SqrtReplOneM = {r[1] -> Sqrt[s23^2 - 2*s23*s45 + s45^2 - 2*s23*s61 - 
       2*s45*s61 + s61^2], r[2] -> Sqrt[mm^2 - 2*mm*s123 + s123^2 - 
       2*mm*s45 - 2*s123*s45 + s45^2], 
    r[3] -> Sqrt[s12^2 - 2*s12*s34 + s34^2 - 2*s12*s56 - 2*s34*s56 + s56^2], 
    r[4] -> Sqrt[mm^2 - 2*mm*s12 + s12^2 - 2*mm*s345 - 2*s12*s345 + s345^2], 
    r[5] -> Sqrt[s12^2*s23^2 - 2*s12^2*s23*s234 + 2*s12*s123*s23*s234 + 
       s12^2*s234^2 - 2*s12*s123*s234^2 + s123^2*s234^2 + 
       2*s12*s123*s23*s34 - 2*s12*s23^2*s34 + 2*s12*s123*s234*s34 - 
       2*s123^2*s234*s34 + 2*s12*s23*s234*s34 + 2*s123*s23*s234*s34 + 
       s123^2*s34^2 - 2*s123*s23*s34^2 + s23^2*s34^2 - 2*s12*s23^2*s56 + 
       2*s12*s23*s234*s56 - 2*s123*s23*s234*s56 - 4*s12*s23*s34*s56 + 
       2*s123*s23*s34*s56 - 2*s23^2*s34*s56 + s23^2*s56^2], 
    r[6] -> Sqrt[s23^2*s34^2 - 2*s23^2*s34*s345 + 2*s23*s234*s34*s345 + 
       s23^2*s345^2 - 2*s23*s234*s345^2 + s234^2*s345^2 + 
       2*s23*s234*s34*s45 - 2*s23*s34^2*s45 + 2*s23*s234*s345*s45 - 
       2*s234^2*s345*s45 + 2*s23*s34*s345*s45 + 2*s234*s34*s345*s45 + 
       s234^2*s45^2 - 2*s234*s34*s45^2 + s34^2*s45^2 - 2*s23*s34^2*s61 + 
       2*s23*s34*s345*s61 - 2*s234*s34*s345*s61 - 4*s23*s34*s45*s61 + 
       2*s234*s34*s45*s61 - 2*s34^2*s45*s61 + s34^2*s61^2], 
    r[7] -> Sqrt[mm^2*s34^2 - 2*mm*s123*s34^2 + s123^2*s34^2 + 
       2*mm*s123*s34*s345 - 2*s123^2*s34*s345 + s123^2*s345^2 + 
       2*mm*s12*s34*s45 - 4*mm*s123*s34*s45 + 2*s12*s123*s34*s45 - 
       2*mm*s34^2*s45 - 2*s123*s34^2*s45 - 2*s12*s123*s345*s45 + 
       2*s123*s34*s345*s45 + s12^2*s45^2 - 2*s12*s34*s45^2 + s34^2*s45^2 - 
       2*mm*s34*s345*s56 + 2*s123*s34*s345*s56 - 2*s123*s345^2*s56 + 
       2*mm*s34*s45*s56 - 4*s12*s34*s45*s56 + 2*s123*s34*s45*s56 + 
       2*s12*s345*s45*s56 + 2*s123*s345*s45*s56 + 2*s34*s345*s45*s56 - 
       2*s12*s45^2*s56 - 2*s34*s45^2*s56 + s345^2*s56^2 - 2*s345*s45*s56^2 + 
       s45^2*s56^2], r[8] -> Sqrt[mm^2*s23^2 - 2*mm^2*s23*s234 + 
       2*mm*s123*s23*s234 + mm^2*s234^2 - 2*mm*s123*s234^2 + s123^2*s234^2 - 
       4*mm*s123*s234*s45 + 2*mm*s23*s234*s45 - 2*mm*s234^2*s45 - 
       2*s123*s234^2*s45 + s234^2*s45^2 - 2*mm*s23^2*s56 + 
       2*mm*s23*s234*s56 - 2*s123*s23*s234*s56 + 2*mm*s23*s45*s56 + 
       2*mm*s234*s45*s56 + 2*s123*s234*s45*s56 + 2*s23*s234*s45*s56 - 
       2*s234*s45^2*s56 + s23^2*s56^2 - 2*s23*s45*s56^2 + s45^2*s56^2 - 
       2*mm*s123*s23*s61 + 2*mm*s123*s234*s61 - 2*s123^2*s234*s61 + 
       2*s123*s234*s45*s61 + 2*mm*s23*s56*s61 + 2*s123*s23*s56*s61 - 
       2*mm*s234*s56*s61 + 2*s123*s234*s56*s61 + 2*s123*s45*s56*s61 - 
       4*s23*s45*s56*s61 + 2*s234*s45*s56*s61 - 2*s23*s56^2*s61 - 
       2*s45*s56^2*s61 + s123^2*s61^2 - 2*s123*s56*s61^2 + s56^2*s61^2], 
    r[9] -> Sqrt[mm^2*s234^2 - 2*mm*s12*s234^2 + s12^2*s234^2 - 
       2*mm^2*s234*s34 + 2*mm*s12*s234*s34 + mm^2*s34^2 - 
       4*mm*s12*s234*s345 - 2*mm*s234^2*s345 - 2*s12*s234^2*s345 + 
       2*mm*s234*s34*s345 + s234^2*s345^2 + 2*mm*s234*s345*s56 + 
       2*s12*s234*s345*s56 - 2*mm*s34*s345*s56 - 2*s234*s345^2*s56 + 
       s345^2*s56^2 + 2*mm*s12*s234*s61 - 2*s12^2*s234*s61 + 
       2*mm*s12*s34*s61 + 2*mm*s234*s34*s61 + 2*s12*s234*s34*s61 - 
       2*mm*s34^2*s61 + 2*s12*s234*s345*s61 - 2*s234*s34*s345*s61 - 
       2*mm*s234*s56*s61 + 2*s12*s234*s56*s61 + 2*mm*s34*s56*s61 - 
       4*s12*s34*s56*s61 + 2*s12*s345*s56*s61 + 2*s234*s345*s56*s61 + 
       2*s34*s345*s56*s61 - 2*s345*s56^2*s61 + s12^2*s61^2 - 
       2*s12*s34*s61^2 + s34^2*s61^2 - 2*s12*s56*s61^2 - 2*s34*s56*s61^2 + 
       s56^2*s61^2], r[10] -> Sqrt[mm^2*s23^2 - 2*mm*s12*s23^2 + 
       s12^2*s23^2 - 4*mm*s12*s23*s345 + 2*mm*s123*s23*s345 + 
       2*s12*s123*s23*s345 - 2*mm*s23^2*s345 - 2*s12*s23^2*s345 + 
       s123^2*s345^2 - 2*s123*s23*s345^2 + s23^2*s345^2 + 2*mm*s12*s23*s45 - 
       2*s12^2*s23*s45 - 2*s12*s123*s345*s45 + 2*s12*s23*s345*s45 + 
       s12^2*s45^2 + 2*mm*s12*s23*s61 - 2*s12^2*s23*s61 - 2*mm*s123*s23*s61 + 
       2*s12*s123*s23*s61 + 2*s12*s123*s345*s61 - 2*s123^2*s345*s61 + 
       2*s12*s23*s345*s61 + 2*s123*s23*s345*s61 - 2*s12^2*s45*s61 + 
       2*s12*s123*s45*s61 - 4*s12*s23*s45*s61 + s12^2*s61^2 - 
       2*s12*s123*s61^2 + s123^2*s61^2], 
    r[11] -> Sqrt[mm^2*s23^2*s34^2 + 2*mm*s123*s23*s234*s34*s345 + 
       s123^2*s234^2*s345^2 + 2*mm*s12*s23*s234*s34*s45 - 
       2*s12*s123*s234^2*s345*s45 + s12^2*s234^2*s45^2 - 
       2*mm*s23^2*s34*s345*s56 - 2*s123*s23*s234*s345^2*s56 + 
       2*s12*s23*s234*s345*s45*s56 + s23^2*s345^2*s56^2 - 
       2*mm*s123*s23*s34^2*s61 - 2*s123^2*s234*s34*s345*s61 + 
       2*s12*s123*s234*s34*s45*s61 + 2*s123*s23*s34*s345*s56*s61 - 
       4*s12*s23*s34*s45*s56*s61 + s123^2*s34^2*s61^2]}
