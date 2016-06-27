bool p384_32_valid(unsigned char *p);
void p384_32_scalarmult(unsigned char *q, const unsigned char *n, const unsigned char *p);
void p384_32_scalarmult_base(unsigned char *q, const unsigned char *n);
void p384_32_double_scalarmult_base(unsigned char *q, const unsigned char *a, const unsigned char *n1, const unsigned char *n2);
