
INTERFACE GCDifc {
    METHOD/Actionset_n (a n)
    METHOD/Actionset_m (a m)
    METHODresult a
}

MODULE GCD_INTEGER_32{
JJJbsvtokami.SymbolTable@408a247c
JJKKJresult LLL a
    result is not an Method (Unspecified)
JJKKJset_m LLL a -> Action
    set_m is not an Method (Unspecified)
JJKKJset_n LLL a -> Action
    set_n is not an Method (Unspecified)
        INTERFACE GCD_INTEGER_32ifc
        FIELD INTEGER_32 n
        FIELD INTEGER_32 m
        METHOD/Rule/Action swap if (((n > m) && (m !=  0))) {
               STORE :n = m 
               STORE :m = n 
        }
        METHOD/Rule/Action sub if (((n <= m) && (m !=  0))) {
               STORE :m = (m - n) 
        }
        METHOD/Action set_n (INTEGER_32 in_n) if ((m ==  0)) {
        STORE :n = in_n 
        }
        METHOD/Action set_m (INTEGER_32 in_m) if ((m ==  0)) {
        STORE :m = in_m 
        }
        METHOD result INTEGER_32 = (n) if ((m ==  0)) {

        }
}
MODULE mkMain{
JJJbsvtokami.SymbolTable@2b491fee
        FIELD GCD_INTEGER_32 gcd
        FIELD INTEGER_1 started
        FIELD INTEGER_32 dv
        METHOD/Rule/Action rl_start if ((started ==  0)) {
               CALL :gcd.set_n(  100)
               CALL :gcd.set_m(  20)
               STORE :started =  1 
        }
        METHOD/Rule/Action rl_display {
               LET a v = gcd.result () 
               STORE :dv = v 
        }
}
