#include <string.h>
#include <assert.h>
#include <stddef.h>

#define RIJN_MAX_ROUNDS 14

typedef enum {
    rijn_128 = 4,   /* number of rows */
    rijn_192 = 6,
    rijn_256 = 8
} rijn_size_t;

/*
 * Rijndael parameters.
 */

typedef struct {
    rijn_size_t rijn_blockrows;
    rijn_size_t rijn_keyrows;
} rijn_param_t;

#define RIJN_PARAM_DEFAULT_INITIALIZER { rijn_128, rijn_256 }
#define RIJN_PARAM_INITIALIZER(BLOCKSZ, KEYSZ) { (BLOCKSZ), (KEYSZ) }

void rijn_param_init(rijn_param_t *, rijn_size_t blocksz, rijn_size_t keysz);

/*
 * Rijndael keys are 128, 192 or 256 bits wide.  There are up to
 * RIJN_MAX_ROUNDS + 1 round keys needed, so the schedule is that big.
 */

typedef unsigned char rijn_unit_t[4];
typedef rijn_unit_t rijn_key_t[8];
typedef rijn_unit_t rijn_block_t[8];
typedef unsigned char rijn_flatblock_t[sizeof (rijn_block_t)];

typedef struct {
    rijn_param_t rijn_param;
    int rijn_nrounds;
    rijn_block_t rijn_roundkey[RIJN_MAX_ROUNDS];
} rijn_keysched_t;

void rijn_sched_key(rijn_keysched_t *, rijn_key_t *, const rijn_param_t *);
void rijn_encrypt(rijn_keysched_t *, unsigned char *, const unsigned char *);
void rijn_decrypt(rijn_keysched_t *, unsigned char *, const unsigned char *);
void rijn_cbc_encrypt(rijn_keysched_t *, unsigned char *iv, unsigned char *out, 
	const unsigned char *in, size_t nblocks);
void rijn_cbc_decrypt(rijn_keysched_t *, unsigned char *iv, unsigned char *out,
	const unsigned char *in, size_t nblocks);
void rijn_cfb_encrypt(rijn_keysched_t *, unsigned char *iv, unsigned char *out,
	const unsigned char *pt, size_t nbytes);
void rijn_cfb_decrypt(rijn_keysched_t *, unsigned char *iv, unsigned char *out,
	const unsigned char *in, size_t nbytes);

#define numrows_to_blocksize(N) (4 * (N))
#define max(a, b) ((a) > (b) ? (a) : (b))

static int log_table[256];
static int antilog_table[256];
static int s_box[256];
static int s_box_inverse[256];
static int rcon[30];

static int
multiply(int a, int b)
{
    if (a != 0 && b != 0)
	return antilog_table[(log_table[a] + log_table[b]) % 255];
    return 0;
}

static void
key_add(rijn_block_t *out, rijn_block_t *in, rijn_block_t *roundkey, int numrows)
{
    unsigned char *flat_out = (unsigned char *) out;
    const unsigned char *flat_in = (unsigned char *) in;
    const unsigned char *flat_rk = (unsigned char *) roundkey;
    int numbytes = numrows_to_blocksize(numrows);

    while (numbytes-- > 0)
	*flat_out++ = *flat_in++ ^ *flat_rk++;
}

static void
shift_column_routine(rijn_block_t *block, rijn_size_t numrows, int inverse)
{
    static int shifts[2][3][4] = {
	{
	    { 0, 1, 2, 3 }, /* shifts for 128 bit block */
	    { 0, 1, 2, 3 }, /* shifts for 192 bit block */
	    { 0, 1, 3, 4 }, /* shifts for 256 bit block */
	}, 
	{
	    { 0, 3, 2, 1 }, /* inverse shifts for 128 bit block */
	    { 0, 5, 4, 3 }, /* inverse shifts for 192 bit block */ 
	    { 0, 7, 5, 4 }, /* inverse shifts for 256 bit block */
	}
    };

    rijn_block_t temp;
    int shift_index = (numrows - 4) / 2;
    int i;
    int *shift_select;

    assert (numrows == rijn_128 || numrows == rijn_192 || numrows == rijn_256);
    assert (shift_index >= 0 && shift_index < 3);
    assert (inverse == 0 || inverse == 1);

    shift_select = shifts[inverse][shift_index];

    /*
     * Create temporary block, with the columns shifted by the amount
     * from the table. The switch is used in order to reduce the
     * modulus to a constant.
     */

    switch (numrows) {
    case rijn_128:
	for (i = 0; i < numrows; i++) {
	    temp[i][0] = (*block)[i][0];
	    temp[i][1] = (*block)[(i + shift_select[1]) % rijn_128][1];
	    temp[i][2] = (*block)[(i + shift_select[2]) % rijn_128][2];
	    temp[i][3] = (*block)[(i + shift_select[3]) % rijn_128][3];
	}
	break;
    case rijn_192:
	for (i = 0; i < numrows; i++) {
	    temp[i][0] = (*block)[i][0];
	    temp[i][1] = (*block)[(i + shift_select[1]) % rijn_192][1];
	    temp[i][2] = (*block)[(i + shift_select[2]) % rijn_192][2];
	    temp[i][3] = (*block)[(i + shift_select[3]) % rijn_192][3];
	}
	break;
    case rijn_256:
	for (i = 0; i < numrows; i++) {
	    temp[i][0] = (*block)[i][0];
	    temp[i][1] = (*block)[(i + shift_select[1]) % rijn_256][1];
	    temp[i][2] = (*block)[(i + shift_select[2]) % rijn_256][2];
	    temp[i][3] = (*block)[(i + shift_select[3]) % rijn_256][3];
	}
	break;
    }

    /*
     * Block is ready, just copy it over
     */

    memcpy(block, &temp, numrows_to_blocksize(numrows));;
}

static void
shift_column(rijn_block_t *block, rijn_size_t numrows)
{
    shift_column_routine(block, numrows, 0);
}

static void
shift_column_inverse(rijn_block_t *block, rijn_size_t numrows)
{
    shift_column_routine(block, numrows, 1);
}

static void
substitute(rijn_block_t *block, int *box, int numrows)
{
    unsigned char *flat_block = (unsigned char *) block;
    int numbytes = numrows_to_blocksize(numrows);

    while (numbytes-- > 0)
	flat_block[numbytes] = box[flat_block[numbytes]];
}

static void
mix_row(rijn_block_t *block, rijn_size_t numrows)
{
    rijn_block_t temp;
    int i, j;

    for (j = 0; j < numrows; j++) {
	for (i = 0; i < 4; i++) {
	    temp[j][i] = multiply(2,(*block)[j][i])
		       ^ multiply(3,(*block)[j][(i + 1) % 4])
		       ^	    (*block)[j][(i + 2) % 4]
		       ^	    (*block)[j][(i + 3) % 4];
	}
    }

    memcpy(block, &temp, numrows_to_blocksize(numrows));
}

static void
mix_row_inverse(rijn_block_t *block, rijn_size_t numrows)
{
    rijn_block_t temp;
    int i, j;

    for (j = 0; j < numrows; j++) {
	for (i = 0; i < 4; i++) {
	    temp[j][i] = multiply(14,(*block)[j][i])
		       ^ multiply(11,(*block)[j][(i + 1) % 4])
		       ^ multiply(13,(*block)[j][(i + 2) % 4])
		       ^ multiply( 9,(*block)[j][(i + 3) % 4]);
	}
    }

    memcpy(block, &temp, numrows_to_blocksize(numrows));
}

void 
rijn_param_init(rijn_param_t *param, rijn_size_t blocksize, rijn_size_t keysize)
{
    assert (blocksize == rijn_128 || blocksize == rijn_192 || blocksize == rijn_256);
    assert (keysize == rijn_128 || keysize == rijn_192 || keysize == rijn_256);

    param->rijn_blockrows = blocksize;
    param->rijn_keyrows = keysize;
}

void 
rijn_sched_key(rijn_keysched_t *sched, rijn_key_t *key, const rijn_param_t *param)
{
    rijn_size_t keyrows = param->rijn_keyrows;
    rijn_size_t blockrows = param->rijn_blockrows;
    rijn_key_t temp_key;
    int keybytes = numrows_to_blocksize(keyrows);
    int row, i, nrounds = 0, rcon_index = 0;

    sched->rijn_param = *param;
    switch (max(keyrows, blockrows)) {
    case rijn_128:
	nrounds = sched->rijn_nrounds = 10;
	break;
    case rijn_192:
	nrounds = sched->rijn_nrounds = 12;
	break;
    case rijn_256:
	nrounds = sched->rijn_nrounds = 14;
	break;
    }

    assert (nrounds != 0);

    memcpy(&temp_key, key, keybytes);

    for (row = 0; row < keyrows; row++) {
	sched->rijn_roundkey[row / blockrows][row % blockrows][0] = temp_key[row][0];
	sched->rijn_roundkey[row / blockrows][row % blockrows][1] = temp_key[row][1];
	sched->rijn_roundkey[row / blockrows][row % blockrows][2] = temp_key[row][2];
	sched->rijn_roundkey[row / blockrows][row % blockrows][3] = temp_key[row][3];
    }

    while (row < (nrounds + 1) * blockrows) {
	temp_key[0][0] ^= s_box[temp_key[keyrows-1][1]];
	temp_key[0][1] ^= s_box[temp_key[keyrows-1][2]];
	temp_key[0][2] ^= s_box[temp_key[keyrows-1][3]];
	temp_key[0][3] ^= s_box[temp_key[keyrows-1][0]];

	temp_key[0][0] ^= rcon[rcon_index++];

	if (keyrows == 8) {
	    for (i = 1; i < keyrows / 2; i++) {
		temp_key[i][0] ^= temp_key[i-1][0];
		temp_key[i][1] ^= temp_key[i-1][1];
		temp_key[i][2] ^= temp_key[i-1][2];
		temp_key[i][3] ^= temp_key[i-1][3];
	    }
	    temp_key[0][i] ^= s_box[temp_key[i-1][0]];
	    temp_key[1][i] ^= s_box[temp_key[i-1][1]];
	    temp_key[2][i] ^= s_box[temp_key[i-1][2]];
	    temp_key[3][i] ^= s_box[temp_key[i-1][3]];
	    for (i++; i < keyrows; i++) {
		temp_key[i][0] ^= temp_key[i-1][0];
		temp_key[i][1] ^= temp_key[i-1][1];
		temp_key[i][2] ^= temp_key[i-1][2];
		temp_key[i][3] ^= temp_key[i-1][3];
	    }
	} else {
	    assert (keyrows != 8);
	    for (i = 1; i < keyrows; i++) {
		temp_key[i][0] ^= temp_key[i-1][0];
		temp_key[i][1] ^= temp_key[i-1][1];
		temp_key[i][2] ^= temp_key[i-1][2];
		temp_key[i][3] ^= temp_key[i-1][3];
	    }
	}

	for (i = 0; i < keyrows && row < (nrounds + 1) * blockrows; i++, row++) {
	    sched->rijn_roundkey[row / blockrows][row % blockrows][0] = temp_key[i][0];
	    sched->rijn_roundkey[row / blockrows][row % blockrows][1] = temp_key[i][1];
	    sched->rijn_roundkey[row / blockrows][row % blockrows][2] = temp_key[i][2];
	    sched->rijn_roundkey[row / blockrows][row % blockrows][3] = temp_key[i][3];
	}
    }
}

void 
rijn_encrypt(rijn_keysched_t *sched, unsigned char *out, const unsigned char *in)
{
    rijn_size_t blockrows = sched->rijn_param.rijn_blockrows;
    int round, nrounds = sched->rijn_nrounds;

    rijn_block_t *out_block = (rijn_block_t *) out;
    rijn_block_t *in_block = (rijn_block_t *) in;

    key_add(out_block, in_block, &sched->rijn_roundkey[0], blockrows);

    for (round = 1; round < nrounds; round++) {
	substitute(out_block, s_box, blockrows);
	shift_column(out_block, blockrows);
	mix_row(out_block, blockrows);
	key_add(out_block, out_block, &sched->rijn_roundkey[round], blockrows);
    }

    substitute(out_block, s_box, blockrows);
    shift_column(out_block, blockrows);
    key_add(out_block, out_block, &sched->rijn_roundkey[round], blockrows);
}

void 
rijn_decrypt(rijn_keysched_t *sched, unsigned char *out, const unsigned char *in)
{
    rijn_size_t blockrows = sched->rijn_param.rijn_blockrows;
    int round, nrounds = sched->rijn_nrounds;

    rijn_block_t *out_block = (rijn_block_t *) out;
    rijn_block_t *in_block = (rijn_block_t *) in;

    key_add(out_block, in_block, &sched->rijn_roundkey[nrounds], blockrows);
    substitute(out_block, s_box_inverse, blockrows);
    shift_column_inverse(out_block, blockrows);

    for (round = nrounds - 1; round > 0; round--) {
	key_add(out_block, out_block, &sched->rijn_roundkey[round], blockrows);
	mix_row_inverse(out_block, blockrows);
	substitute(out_block, s_box_inverse, blockrows);
	shift_column_inverse(out_block, blockrows);
    }

    assert (round == 0);
    key_add(out_block, out_block, &sched->rijn_roundkey[round], blockrows);
}

static 
void xor_mem(unsigned char *dest, const unsigned char *a, 
	const unsigned char *b, size_t n)
{
    while (n--)
	*dest++ = *a++ ^ *b++;
}

void 
rijn_cbc_encrypt(rijn_keysched_t *sched, unsigned char *iv, unsigned char *out, 
	const unsigned char *in, size_t nblocks)
{
    unsigned char *ivec = iv;
    size_t blocksize = numrows_to_blocksize(sched->rijn_param.rijn_blockrows);
    size_t i, nbytes = nblocks * blocksize;

    for (i = 0; i < nbytes; i += blocksize) {
	xor_mem(out + i, in + i, ivec, blocksize);
	rijn_encrypt(sched, out + i, out + i);
	ivec = out + i;
    }

    memcpy(iv, ivec, blocksize);
}

void 
rijn_cbc_decrypt(rijn_keysched_t *sched, unsigned char *iv, unsigned char *out,
	const unsigned char *in, size_t nblocks)
{
    rijn_block_t iv_save;
    size_t blocksize = numrows_to_blocksize(sched->rijn_param.rijn_blockrows);
    size_t i, nbytes = nblocks * blocksize;

    if (nblocks > 0) {
	memcpy(&iv_save, in + nbytes - blocksize, blocksize);

	for (i = nbytes - blocksize; i < nbytes; i -= blocksize) {
	    const unsigned char *ivec = (i > 0) ? in + i - blocksize : iv;
	    rijn_decrypt(sched, out + i, in + i);
	    xor_mem(out + i, out + i, ivec, blocksize);
	}

	memcpy(iv, &iv_save, blocksize);
    }
}

extern int putchar (int);
int printf(const char *, ...);

static void hex_dump(const unsigned char *data, size_t size)
{
    while (size--)
	printf("%02X", (unsigned int) *data++);
}

int main(void)
{
    static rijn_param_t param = RIJN_PARAM_INITIALIZER(rijn_128, rijn_192);
    rijn_key_t key = { { 0x80 } };
    rijn_keysched_t sched = { { 0 } };
    unsigned char plaintext[32] = { 0 };
    unsigned char ciphertext[32] = { 0 };

    rijn_sched_key(&sched, &key, &param);
    rijn_encrypt(&sched, ciphertext, plaintext);
    hex_dump(ciphertext, 16);
    putchar('\n');
    rijn_decrypt(&sched, plaintext, ciphertext);
    hex_dump(plaintext, 16);
    putchar('\n');
    return 0;
}



static int log_table[256] = {
  0,   0,  25,	 1,  50,   2,  26, 198,  75, 199,  27, 104,  51, 238, 223,   3,
100,   4, 224,	14,  52, 141, 129, 239,  76, 113,   8, 200, 248, 105,  28, 193,
125, 194,  29, 181, 249, 185,  39, 106,  77, 228, 166, 114, 154, 201,	9, 120,
101,  47, 138,	 5,  33,  15, 225,  36,  18, 240, 130,	69,  53, 147, 218, 142,
150, 143, 219, 189,  54, 208, 206, 148,  19,  92, 210, 241,  64,  70, 131,  56,
102, 221, 253,	48, 191,   6, 139,  98, 179,  37, 226, 152,  34, 136, 145,  16,
126, 110,  72, 195, 163, 182,  30,  66,  58, 107,  40,	84, 250, 133,  61, 186,
 43, 121,  10,	21, 155, 159,  94, 202,  78, 212, 172, 229, 243, 115, 167,  87,
175,  88, 168,	80, 244, 234, 214, 116,  79, 174, 233, 213, 231, 230, 173, 232,
 44, 215, 117, 122, 235,  22,  11, 245,  89, 203,  95, 176, 156, 169,  81, 160,
127,  12, 246, 111,  23, 196,  73, 236, 216,  67,  31,	45, 164, 118, 123, 183,
204, 187,  62,	90, 251,  96, 177, 134,  59,  82, 161, 108, 170,  85,  41, 157,
151, 178, 135, 144,  97, 190, 220, 252, 188, 149, 207, 205,  55,  63,  91, 209,
 83,  57, 132,	60,  65, 162, 109,  71,  20,  42, 158,	93,  86, 242, 211, 171,
 68,  17, 146, 217,  35,  32,  46, 137, 180, 124, 184,	38, 119, 153, 227, 165,
103,  74, 237, 222, 197,  49, 254,  24,  13,  99, 140, 128, 192, 247, 112,   7
};

static int antilog_table[256] = {
  1,   3,   5,	15,  17,  51,  85, 255,  26,  46, 114, 150, 161, 248,  19,  53, 
 95, 225,  56,	72, 216, 115, 149, 164, 247,   2,   6,	10,  30,  34, 102, 170, 
229,  52,  92, 228,  55,  89, 235,  38, 106, 190, 217, 112, 144, 171, 230,  49, 
 83, 245,   4,	12,  20,  60,  68, 204,  79, 209, 104, 184, 211, 110, 178, 205, 
 76, 212, 103, 169, 224,  59,  77, 215,  98, 166, 241,	 8,  24,  40, 120, 136, 
131, 158, 185, 208, 107, 189, 220, 127, 129, 152, 179, 206,  73, 219, 118, 154, 
181, 196,  87, 249,  16,  48,  80, 240,  11,  29,  39, 105, 187, 214,  97, 163, 
254,  25,  43, 125, 135, 146, 173, 236,  47, 113, 147, 174, 233,  32,  96, 160, 
251,  22,  58,	78, 210, 109, 183, 194,  93, 231,  50,	86, 250,  21,  63,  65, 
195,  94, 226,	61,  71, 201,  64, 192,  91, 237,  44, 116, 156, 191, 218, 117, 
159, 186, 213, 100, 172, 239,  42, 126, 130, 157, 188, 223, 122, 142, 137, 128, 
155, 182, 193,	88, 232,  35, 101, 175, 234,  37, 111, 177, 200,  67, 197,  84, 
252,  31,  33,	99, 165, 244,	7,   9,  27,  45, 119, 153, 176, 203,  70, 202, 
 69, 207,  74, 222, 121, 139, 134, 145, 168, 227,  62,	66, 198,  81, 243,  14, 
 18,  54,  90, 238,  41, 123, 141, 140, 143, 138, 133, 148, 167, 242,  13,  23, 
 57,  75, 221, 124, 132, 151, 162, 253,  28,  36, 108, 180, 199,  82, 246,   1, 
}; 

static int s_box[256] = {
 99, 124, 119, 123, 242, 107, 111, 197,  48,   1, 103,	43, 254, 215, 171, 118,
202, 130, 201, 125, 250,  89,  71, 240, 173, 212, 162, 175, 156, 164, 114, 192,
183, 253, 147,	38,  54,  63, 247, 204,  52, 165, 229, 241, 113, 216,  49,  21,
  4, 199,  35, 195,  24, 150,	5, 154,   7,  18, 128, 226, 235,  39, 178, 117,
  9, 131,  44,	26,  27, 110,  90, 160,  82,  59, 214, 179,  41, 227,  47, 132,
 83, 209,   0, 237,  32, 252, 177,  91, 106, 203, 190,	57,  74,  76,  88, 207,
208, 239, 170, 251,  67,  77,  51, 133,  69, 249,   2, 127,  80,  60, 159, 168,
 81, 163,  64, 143, 146, 157,  56, 245, 188, 182, 218,	33,  16, 255, 243, 210,
205,  12,  19, 236,  95, 151,  68,  23, 196, 167, 126,	61, 100,  93,  25, 115,
 96, 129,  79, 220,  34,  42, 144, 136,  70, 238, 184,	20, 222,  94,  11, 219,
224,  50,  58,	10,  73,   6,  36,  92, 194, 211, 172,	98, 145, 149, 228, 121,
231, 200,  55, 109, 141, 213,  78, 169, 108,  86, 244, 234, 101, 122, 174,   8,
186, 120,  37,	46,  28, 166, 180, 198, 232, 221, 116,	31,  75, 189, 139, 138,
112,  62, 181, 102,  72,   3, 246,  14,  97,  53,  87, 185, 134, 193,  29, 158,
225, 248, 152,	17, 105, 217, 142, 148, 155,  30, 135, 233, 206,  85,  40, 223,
140, 161, 137,	13, 191, 230,  66, 104,  65, 153,  45,	15, 176,  84, 187,  22,
};

static int s_box_inverse[256] = {
 82,   9, 106, 213,  48,  54, 165,  56, 191,  64, 163, 158, 129, 243, 215, 251,
124, 227,  57, 130, 155,  47, 255, 135,  52, 142,  67,	68, 196, 222, 233, 203,
 84, 123, 148,	50, 166, 194,  35,  61, 238,  76, 149,	11,  66, 250, 195,  78,
  8,  46, 161, 102,  40, 217,  36, 178, 118,  91, 162,	73, 109, 139, 209,  37,
114, 248, 246, 100, 134, 104, 152,  22, 212, 164,  92, 204,  93, 101, 182, 146,
108, 112,  72,	80, 253, 237, 185, 218,  94,  21,  70,	87, 167, 141, 157, 132,
144, 216, 171,	 0, 140, 188, 211,  10, 247, 228,  88,	 5, 184, 179,  69,   6,
208,  44,  30, 143, 202,  63,  15,   2, 193, 175, 189,	 3,   1,  19, 138, 107,
 58, 145,  17,	65,  79, 103, 220, 234, 151, 242, 207, 206, 240, 180, 230, 115,
150, 172, 116,	34, 231, 173,  53, 133, 226, 249,  55, 232,  28, 117, 223, 110,
 71, 241,  26, 113,  29,  41, 197, 137, 111, 183,  98,	14, 170,  24, 190,  27,
252,  86,  62,	75, 198, 210, 121,  32, 154, 219, 192, 254, 120, 205,  90, 244,
 31, 221, 168,	51, 136,   7, 199,  49, 177,  18,  16,	89,  39, 128, 236,  95,
 96,  81, 127, 169,  25, 181,  74,  13,  45, 229, 122, 159, 147, 201, 156, 239,
160, 224,  59,	77, 174,  42, 245, 176, 200, 235, 187,	60, 131,  83, 153,  97,
 23,  43,   4, 126, 186, 119, 214,  38, 225, 105,  20,	99,  85,  33,  12, 125,
};

static int rcon[30] = {
    0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8,
    0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4,
    0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91
};
