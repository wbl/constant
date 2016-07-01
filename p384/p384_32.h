bool p384_32_valid(unsigned char p[96]);
void p384_32_scalarmult(unsigned char q[96], const unsigned char n[48],
                        const unsigned char p[96]);
void p384_32_scalarmult_base(unsigned char q[96], const unsigned char n[48]);
void p384_32_double_scalarmult_base(unsigned char* q, const unsigned char* a,
                                    const unsigned char* n1,
                                    const unsigned char* n2);
