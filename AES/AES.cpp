// ============================================================
//  AES-128 Implementation
//  ACM Summer School — Symmetric Key Cryptography
//
//  Implements AES-128 encryption and decryption from scratch,
//  verified against test vectors.
//
//  Boilerplate/helper functions provided by course instructor.
//  Core AES logic implemented by student.
// ============================================================

#include <iostream>
#include <vector>
#include <string>
#include <bitset>
#include <iomanip>
#include <sstream>
#include <cstdint>
#include <algorithm>
#include <array>

// AES operates on a 4x4 matrix of bytes called the State.
// state[row][col], rows 0-3, cols 0-3.
using State = std::array<std::array<uint8_t, 4>, 4>;

// ============================================================
//  LOOKUP TABLES  (provided by instructor — do not modify)
// ============================================================

//  S-box - provides non-linear byte substitution
// Each byte is replaced by its corresponding entry in this table, causing there to not be any algebraic relation between input and output
static const uint8_t SBOX[256] = {
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5,
    0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0,
    0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc,
    0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a,
    0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0,
    0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b,
    0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85,
    0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5,
    0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17,
    0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88,
    0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c,
    0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9,
    0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6,
    0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e,
    0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94,
    0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68,
    0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16
};

// Inverse S-box - used in decryption to reverse SubBytes
// If SBOX[x] = y, then INV_SBOX[y] = x
static const uint8_t INV_SBOX[256] = {
    0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38,
    0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
    0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87,
    0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
    0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d,
    0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
    0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2,
    0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
    0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16,
    0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
    0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda,
    0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
    0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a,
    0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
    0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02,
    0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
    0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea,
    0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
    0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85,
    0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
    0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89,
    0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
    0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20,
    0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
    0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31,
    0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
    0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d,
    0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
    0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0,
    0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
    0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26,
    0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d
};

// Round constants for key expansion (indices 1-10 used for AES-128).
// Each value is a power of 2 in GF(2^8), ensuring every round key is unique.
// Without these, symmetric keys could produce identical round keys.
static const uint8_t RCON[11] = {
    0x00,  // unused (index 0)
    0x01, 0x02, 0x04, 0x08, 0x10,
    0x20, 0x40, 0x80, 0x1b, 0x36
};

// ============================================================
//  HELPER FUNCTIONS  (provided by instructor)
// ============================================================

// Convert a hex string (e.g. "00112233...EEFF") to a byte vector.
// Pads with trailing zeros if shorter than 32 chars (16 bytes).
std::vector<uint8_t> hexStringToBytes(const std::string& hex) {
    std::string h = hex;
    if (h.size() < 32) h.resize(32, '0');
    else if (h.size() > 32) h = h.substr(0, 32);
    std::vector<uint8_t> bytes;
    for (size_t i = 0; i + 1 < h.size(); i += 2) {
        uint8_t hi = 0, lo = 0;
        char ch = h[i], cl = h[i + 1];
        if (ch >= '0' && ch <= '9')      hi = ch - '0';
        else if (ch >= 'A' && ch <= 'F') hi = ch - 'A' + 10;
        else if (ch >= 'a' && ch <= 'f') hi = ch - 'a' + 10;
        if (cl >= '0' && cl <= '9')      lo = cl - '0';
        else if (cl >= 'A' && cl <= 'F') lo = cl - 'A' + 10;
        else if (cl >= 'a' && cl <= 'f') lo = cl - 'a' + 10;
        bytes.push_back(static_cast<uint8_t>((hi << 4) | lo));
    }
    return bytes;
}

// Convert a byte vector to an uppercase hex string.
std::string bytesToHexString(const std::vector<uint8_t>& bytes) {
    std::ostringstream oss;
    oss << std::uppercase << std::hex << std::setfill('0');
    for (uint8_t b : bytes)
        oss << std::setw(2) << static_cast<int>(b);
    return oss.str();
}

// ============================================================
//  GF(2^8) ARITHMETIC
//  AES arithmetic stays within 0-255 using the finite field
// ============================================================

// Multiply by 2 in GF(2^8).
// Left shift by 1 (multiply by 2), then XOR with 0x1b if the
// top bit was set before shifting to prevent overflow past 8 bits.
static uint8_t xtime(uint8_t a) {
    return (a << 1) ^ (a & 0x80 ? 0x1b : 0x00);
}

static uint8_t gmul(uint8_t a, uint8_t b) {
    uint8_t result = 0;
    while (b) {
        if (b & 1) result ^= a;   // if lowest bit set, add a to result
        a = xtime(a);              // double a for the next bit position
        b >>= 1;                   // move to the next bit of b
    }
    return result;
}

// ============================================================
//  KEY EXPANSION
//  Expands the 16-byte key into 44 words (11 round keys x 4 words).
//  Each round of AES needs its own unique 16-byte key derived
//  from the original, so no two rounds share the same key material.
// ============================================================
std::vector<uint32_t> keyExpansion(const std::vector<uint8_t>& key) {
    std::vector<uint32_t> w(44);

    // The first 4 words are loaded directly from the original key,
    for (int i = 0; i < 4; i++) {
        w[i] = ((uint32_t)key[4*i]     << 24) |
               ((uint32_t)key[4*i + 1] << 16) |
               ((uint32_t)key[4*i + 2] <<  8) |
               ((uint32_t)key[4*i + 3]);
    }

    for (int i = 4; i < 44; i++) {
        uint32_t temp = w[i - 1];

        // Every 4th word undergoes three transformations to introduce non-linearity and prevent round keys from being too similar.
        if (i % 4 == 0) {

            // RotWord: rotate left by one byte so the schedule doesn't
            // always apply SubWord to the same byte position each round.
            // e.g. 0xAABBCCDD -> 0xBBCCDDAA
            // (temp << 8) shifts three bytes left; (temp >> 24) wraps
            // the leftmost byte around to the rightmost position.
            temp = (temp << 8) | (temp >> 24);

            // SubWord: apply the SBOX to each byte of the word, adding non-linearity so round keys can't be algebraically related to each other even if the original key is simple.
            temp = ((uint32_t)SBOX[(temp >> 24) & 0xFF] << 24) |
                   ((uint32_t)SBOX[(temp >> 16) & 0xFF] << 16) |
                   ((uint32_t)SBOX[(temp >>  8) & 0xFF] <<  8) |
                   ((uint32_t)SBOX[(temp      ) & 0xFF]);

            // XOR with the round constant (top byte only)
            // Eliminates symmetry — without this, identical half-keys would produce identical round keys, weakening security
            temp ^= ((uint32_t)RCON[i / 4] << 24);
        }

        // Each word is XORed with the word four positions back
        w[i] = w[i - 4] ^ temp;
    }

    return w;
}

// ============================================================
//  SUB BYTES
//  Applies the AES S-box to every byte in the state independently
//  This is the only non-linear step in AES — it ensures the cipher cannot be described as a simple system of linear equations, making algebraic attacks infeasible
// ============================================================
void subBytes(State& state) {
    for (int row = 0; row < 4; row++)
        for (int col = 0; col < 4; col++)
            state[row][col] = SBOX[state[row][col]];
}

// Inverse: uses INV_SBOX to reverse the substitution during decryption.
void invSubBytes(State& state) {
    for (int row = 0; row < 4; row++)
        for (int col = 0; col < 4; col++)
            state[row][col] = INV_SBOX[state[row][col]];
}

// ============================================================
//  SHIFT ROWS
//  Cyclically shifts each row of the state left by its row index to achieve full diffusion of the whole block
// ============================================================
void shiftRows(State& state) {
    // Row 0: no shift

    // Row 1: shift left by 1 — save leftmost byte, shift others left, wrap saved byte to right
    uint8_t tmp = state[1][0];
    state[1][0] = state[1][1];
    state[1][1] = state[1][2];
    state[1][2] = state[1][3];
    state[1][3] = tmp;

    // Row 2: shift left by 2 — swapping opposite pairs achieves this in two moves
    std::swap(state[2][0], state[2][2]);
    std::swap(state[2][1], state[2][3]);

    // Row 3: shift left by 3 = shift right by 1 — wrap rightmost byte to leftmost
    tmp = state[3][3];
    state[3][3] = state[3][2];
    state[3][2] = state[3][1];
    state[3][1] = state[3][0];
    state[3][0] = tmp;
}

// Inverse: shifts right instead of left (right by 1, 2, 3 for rows 1, 2, 3).
void invShiftRows(State& state) {
    // Row 0: no shift

    // Row 1: shift right by 1
    uint8_t tmp = state[1][3];
    state[1][3] = state[1][2];
    state[1][2] = state[1][1];
    state[1][1] = state[1][0];
    state[1][0] = tmp;

    // Row 2: shift right by 2 (same as left by 2)
    std::swap(state[2][0], state[2][2]);
    std::swap(state[2][1], state[2][3]);

    // Row 3: shift right by 3 = shift left by 1
    tmp = state[3][0];
    state[3][0] = state[3][1];
    state[3][1] = state[3][2];
    state[3][2] = state[3][3];
    state[3][3] = tmp;
}

// ============================================================
//  MIX COLUMNS
//  Treats each column as a 4-byte polynomial and multiplies it by a fixed matrix in GF(2^8).
//  Every output byte depends on all 4 input bytes of its column
//
//  Forward matrix: [2,3,1,1 / 1,2,3,1 / 1,1,2,3 / 3,1,1,2]
//  Multiply by 2 = xtime(a)
//  Multiply by 3 = xtime(a) XOR a
//  Multiply by 1 = a (unchanged)
//  Addition in GF(2^8) = XOR
// ============================================================
void mixColumns(State& state) {
    for (int col = 0; col < 4; col++) {
        // Save original column values before any modification
        uint8_t s0 = state[0][col];
        uint8_t s1 = state[1][col];
        uint8_t s2 = state[2][col];
        uint8_t s3 = state[3][col];

        state[0][col] = xtime(s0) ^ (xtime(s1) ^ s1) ^ s2              ^ s3;
        state[1][col] = s0        ^ xtime(s1)         ^ (xtime(s2)^s2) ^ s3;
        state[2][col] = s0        ^ s1                ^ xtime(s2)       ^ (xtime(s3)^s3);
        state[3][col] = (xtime(s0)^s0) ^ s1           ^ s2              ^ xtime(s3);
    }
}

// Inverse: uses the inverse matrix [14,11,13,9 / 9,14,11,13 / 13,9,14,11 / 11,13,9,14].
// Larger multipliers require the full gmul function rather than just xtime.
void invMixColumns(State& state) {
    for (int col = 0; col < 4; col++) {
        uint8_t s0 = state[0][col];
        uint8_t s1 = state[1][col];
        uint8_t s2 = state[2][col];
        uint8_t s3 = state[3][col];

        state[0][col] = gmul(s0,14) ^ gmul(s1,11) ^ gmul(s2,13) ^ gmul(s3, 9);
        state[1][col] = gmul(s0, 9) ^ gmul(s1,14) ^ gmul(s2,11) ^ gmul(s3,13);
        state[2][col] = gmul(s0,13) ^ gmul(s1, 9) ^ gmul(s2,14) ^ gmul(s3,11);
        state[3][col] = gmul(s0,11) ^ gmul(s1,13) ^ gmul(s2, 9) ^ gmul(s3,14);
    }
}

// ============================================================
//  ADD ROUND KEY
//  XORs the current state with the round key for the given round.
//  This is the only step that directly involves the key, tying
//  the entire cipher to the secret. XOR is its own inverse, so
//  the same function works identically for both encrypt and decrypt.
// ============================================================
void addRoundKey(State& state, const std::vector<uint32_t>& expandedKey, int round) {
    for (int col = 0; col < 4; col++) {
        // Each word covers one column; extract bytes from most to least significant
        uint32_t word = expandedKey[round * 4 + col];
        state[0][col] ^= (word >> 24) & 0xFF;
        state[1][col] ^= (word >> 16) & 0xFF;
        state[2][col] ^= (word >>  8) & 0xFF;
        state[3][col] ^= (word      ) & 0xFF;
    }
}

// ============================================================
//  AES-128 ENCRYPTION
//  Plaintext and key are both 16 bytes. Returns 16-byte ciphertext.
//
//  Structure:
//    Round 0:    AddRoundKey only (key whitening)
//    Rounds 1-9: SubBytes -> ShiftRows -> MixColumns -> AddRoundKey
//    Round 10:   SubBytes -> ShiftRows -> AddRoundKey (no MixColumns)
//
//  MixColumns is omitted in the final round because it would be immediately undone at the start of decryption, adding no security.
// ============================================================
std::vector<uint8_t> aesEncrypt(const std::vector<uint8_t>& plaintext,
                                 const std::vector<uint8_t>& key) {
    auto expandedKey = keyExpansion(key);

    // Load plaintext into the state in column-major order:
    // bytes 0-3 fill column 0 top to bottom, bytes 4-7 fill column 1, etc.
    State state;
    for (int col = 0; col < 4; col++)
        for (int row = 0; row < 4; row++)
            state[row][col] = plaintext[col * 4 + row];

    // Round 0: XOR with the original key before any transformation
    addRoundKey(state, expandedKey, 0);

    // Rounds 1-9: all four operations in sequence
    for (int round = 1; round <= 9; round++) {
        subBytes(state);
        shiftRows(state);
        mixColumns(state);
        addRoundKey(state, expandedKey, round);
    }

    // Round 10: final round skips MixColumns
    subBytes(state);
    shiftRows(state);
    addRoundKey(state, expandedKey, 10);

    // Read ciphertext back out of the state in column-major order
    std::vector<uint8_t> ciphertext(16);
    for (int col = 0; col < 4; col++)
        for (int row = 0; row < 4; row++)
            ciphertext[col * 4 + row] = state[row][col];

    return ciphertext;
}

// ============================================================
//  AES-128 DECRYPTION
//  Runs every step of encryption in reverse order using inverse operations
//  The expanded key is the same as encryption, round keys are just applied in reverse (10 down to 0)
// ============================================================
std::vector<uint8_t> aesDecrypt(const std::vector<uint8_t>& ciphertext,
                                 const std::vector<uint8_t>& key) {
    auto expandedKey = keyExpansion(key);

    // Load ciphertext into state in column-major order
    State state;
    for (int col = 0; col < 4; col++)
        for (int row = 0; row < 4; row++)
            state[row][col] = ciphertext[col * 4 + row];

    // Undo round 10 (which had no MixColumns, so none to undo here)
    addRoundKey(state, expandedKey, 10);

    // Undo rounds 9 down to 1 in reverse order with inverse operations.

    for (int round = 9; round >= 1; round--) {
        invShiftRows(state);
        invSubBytes(state);
        addRoundKey(state, expandedKey, round);
        invMixColumns(state);
    }

    // Undo round 0 (key whitening only — no MixColumns to undo)
    invShiftRows(state);
    invSubBytes(state);
    addRoundKey(state, expandedKey, 0);

    // Read plaintext back out of state in column-major order
    std::vector<uint8_t> plaintext(16);
    for (int col = 0; col < 4; col++)
        for (int row = 0; row < 4; row++)
            plaintext[col * 4 + row] = state[row][col];

    return plaintext;
}

// ============================================================
//  MAIN — sample driver
// ============================================================
int main() {
    std::string ptHex  = "00112233445566778899AABBCCDDEEFF";
    std::string keyHex = "000102030405060708090A0B0C0D0E0F";

    std::vector<uint8_t> plaintext = hexStringToBytes(ptHex);
    std::vector<uint8_t> key       = hexStringToBytes(keyHex);

    std::cout << "===== AES-128 Encryption/Decryption =====\n";
    std::cout << "Plaintext : " << ptHex  << "\n";
    std::cout << "Key       : " << keyHex << "\n";

    std::vector<uint8_t> ciphertext = aesEncrypt(plaintext, key);
    std::cout << "Ciphertext: " << bytesToHexString(ciphertext) << "\n";

    std::vector<uint8_t> recovered = aesDecrypt(ciphertext, key);
    std::cout << "Recovered : " << bytesToHexString(recovered) << "\n";

    return 0;
}