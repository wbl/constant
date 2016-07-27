bool p384_64_valid(unsigned char p[96]);
void p384_64_scalarmult(unsigned char q[96], const unsigned char n[48],
                        const unsigned char p[96]);
void p384_64_scalarmult_base(unsigned char q[96], const unsigned char n[48]);
void p384_64_double_scalarmult_base(unsigned char* q, const unsigned char* a,
                                    const unsigned char* n1,
                                    const unsigned char* n2);
