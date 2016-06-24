#need to print constants as arrays of 32 bit ints

radix = 2**32
def print32(x):
    for i in range(1, 12):
        print "0x%x,"%(x % radix)
        x = x/radix

prime = 2**384-2**128-2**96+2**32-1
Rsqr = 2**(384*2)
print32(Rsqr % prime)

