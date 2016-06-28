#need to print constants as arrays of 32 bit ints

radix = 2**32
def print32(x):
    for i in range(0, 12):
        print "0x%x,"%(x % radix)
        x = x/radix

prime = 2**384-2**128-2**96+2**32-1
Rsqr = 2**(384*2)
R = 2**384
base_x = 0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7
base_y = 0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f
curve_b = 27580193559959705877849011840389048093056905856361568521428707301988689241309860865136260764883745107765439761230575
print "Rsqr"
print32(Rsqr % prime)
print "R"
print32(R % prime)
print "prime"
print32(prime)
print "curve_b"
print32(curve_b)
print "base_x"
print32(base_x)
print "base_y"
print32(base_y)
print "y^2+3x^2-b", (base_y**2-base_x**3+3*base_x-curve_b) % prime
