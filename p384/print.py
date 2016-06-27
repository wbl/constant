#need to print constants as arrays of 32 bit ints

radix = 2**32
def print32(x):
    for i in range(0, 12):
        print "0x%x,"%(x % radix)
        x = x/radix

prime = 2**384-2**128-2**96+2**32-1
Rsqr = 2**(384*2)
R = 2**384
print "Rsqr"
print32(Rsqr % prime)
print "R"
print32(R % prime)
print "prime"
print32(prime)
