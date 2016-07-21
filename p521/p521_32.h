bool p521_32_valid(const unsigned char p[132]);
void p521_32_scalarmult(unsigned char q[132], const unsigned char n[66],
                        const unsigned char p[132]);
void p521_32_scalarmult_base(unsigned char q[132], const unsigned char n[66]);
void p521_32_double_scalarmult_base(unsigned char q[132], const unsigned char a[132],
                                    const unsigned char n1[66],
                                    const unsigned char n2[66]);
