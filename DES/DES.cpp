// ============================================================
//  DES Implementation
//  ACM Summer School — Symmetric Key Cryptography
//
//  Implements DES encryption and decryption, verified against test vectors.
//
//  Boilerplate/helper functions provided by course instructor.
//  Core DES logic implemented by student.
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

// ============================================================
//  LOOKUP TABLES  (provided by instructor — do not modify)
// ============================================================

// Initial Permutation — applied to the 64-bit plaintext block before any rounds.
// Rearranges bits according to the DES standard; undone by FP at the end.
static const int IP[64] = {
    58, 50, 42, 34, 26, 18, 10,  2,
    60, 52, 44, 36, 28, 20, 12,  4,
    62, 54, 46, 38, 30, 22, 14,  6,
    64, 56, 48, 40, 32, 24, 16,  8,
    57, 49, 41, 33, 25, 17,  9,  1,
    59, 51, 43, 35, 27, 19, 11,  3,
    61, 53, 45, 37, 29, 21, 13,  5,
    63, 55, 47, 39, 31, 23, 15,  7
};

// Final Permutation — exact inverse of IP, applied at the end after all the 16 rounds
static const int FP[64] = {
    40,  8, 48, 16, 56, 24, 64, 32,
    39,  7, 47, 15, 55, 23, 63, 31,
    38,  6, 46, 14, 54, 22, 62, 30,
    37,  5, 45, 13, 53, 21, 61, 29,
    36,  4, 44, 12, 52, 20, 60, 28,
    35,  3, 43, 11, 51, 19, 59, 27,
    34,  2, 42, 10, 50, 18, 58, 26,
    33,  1, 41,  9, 49, 17, 57, 25
};

// Expansion table — expands the 32-bit right half to 48 bits inside the Feistel function
// Some bits are repeated so that it matches the 48-bit round key width for XOR
static const int E[48] = {
    32,  1,  2,  3,  4,  5,
     4,  5,  6,  7,  8,  9,
     8,  9, 10, 11, 12, 13,
    12, 13, 14, 15, 16, 17,
    16, 17, 18, 19, 20, 21,
    20, 21, 22, 23, 24, 25,
    24, 25, 26, 27, 28, 29,
    28, 29, 30, 31, 32,  1
};

// P permutation — applied to the 32-bit S-box output inside the Feistel function
// Spreads the S-box outputs across different bit positions to increase diffusion
static const int P[32] = {
    16,  7, 20, 21, 29, 12, 28, 17,
     1, 15, 23, 26,  5, 18, 31, 10,
     2,  8, 24, 14, 32, 27,  3,  9,
    19, 13, 30,  6, 22, 11,  4, 25
};

// PC-1 — first key permutation, reduces the 64-bit key to 56 bits by dropping the 8 parity bits (bits 8, 16, 24, 32, 40, 48, 56, 64)
static const int PC1[56] = {
    57, 49, 41, 33, 25, 17,  9,
     1, 58, 50, 42, 34, 26, 18,
    10,  2, 59, 51, 43, 35, 27,
    19, 11,  3, 60, 52, 44, 36,
    63, 55, 47, 39, 31, 23, 15,
     7, 62, 54, 46, 38, 30, 22,
    14,  6, 61, 53, 45, 37, 29,
    21, 13,  5, 28, 20, 12,  4
};

// PC-2 — second key permutation, reduces each 56-bit CD pair to a 48-bit round key.
static const int PC2[48] = {
    14, 17, 11, 24,  1,  5,
     3, 28, 15,  6, 21, 10,
    23, 19, 12,  4, 26,  8,
    16,  7, 27, 20, 13,  2,
    41, 52, 31, 37, 47, 55,
    30, 40, 51, 45, 33, 48,
    44, 49, 39, 56, 34, 53,
    46, 42, 50, 36, 29, 32
};

// Left-shift amounts per round — used during key schedule generation.
// Rounds 1, 2, 9, 16 shift by 1; all others shift by 2.
static const int SHIFT_TABLE[16] = {
    1, 1, 2, 2, 2, 2, 2, 2,
    1, 2, 2, 2, 2, 2, 2, 1
};

// Eight S-boxes — non-linear component of DES.
// Each takes a 6-bit input and produces a 4-bit output,
// indexed by [sbox index][row 0-3][col 0-15].
// Row is determined by the first and last bits; column by the middle four bits.
static const int SBOX[8][4][16] = {
    // S1
    {
        {14,  4, 13,  1,  2, 15, 11,  8,  3, 10,  6, 12,  5,  9,  0,  7},
        { 0, 15,  7,  4, 14,  2, 13,  1, 10,  6, 12, 11,  9,  5,  3,  8},
        { 4,  1, 14,  8, 13,  6,  2, 11, 15, 12,  9,  7,  3, 10,  5,  0},
        {15, 12,  8,  2,  4,  9,  1,  7,  5, 11,  3, 14, 10,  0,  6, 13}
    },
    // S2
    {
        {15,  1,  8, 14,  6, 11,  3,  4,  9,  7,  2, 13, 12,  0,  5, 10},
        { 3, 13,  4,  7, 15,  2,  8, 14, 12,  0,  1, 10,  6,  9, 11,  5},
        { 0, 14,  7, 11, 10,  4, 13,  1,  5,  8, 12,  6,  9,  3,  2, 15},
        {13,  8, 10,  1,  3, 15,  4,  2, 11,  6,  7, 12,  0,  5, 14,  9}
    },
    // S3
    {
        {10,  0,  9, 14,  6,  3, 15,  5,  1, 13, 12,  7, 11,  4,  2,  8},
        {13,  7,  0,  9,  3,  4,  6, 10,  2,  8,  5, 14, 12, 11, 15,  1},
        {13,  6,  4,  9,  8, 15,  3,  0, 11,  1,  2, 12,  5, 10, 14,  7},
        { 1, 10, 13,  0,  6,  9,  8,  7,  4, 15, 14,  3, 11,  5,  2, 12}
    },
    // S4
    {
        { 7, 13, 14,  3,  0,  6,  9, 10,  1,  2,  8,  5, 11, 12,  4, 15},
        {13,  8, 11,  5,  6, 15,  0,  3,  4,  7,  2, 12,  1, 10, 14,  9},
        {10,  6,  9,  0, 12, 11,  7, 13, 15,  1,  3, 14,  5,  2,  8,  4},
        { 3, 15,  0,  6, 10,  1, 13,  8,  9,  4,  5, 11, 12,  7,  2, 14}
    },
    // S5
    {
        { 2, 12,  4,  1,  7, 10, 11,  6,  8,  5,  3, 15, 13,  0, 14,  9},
        {14, 11,  2, 12,  4,  7, 13,  1,  5,  0, 15, 10,  3,  9,  8,  6},
        { 4,  2,  1, 11, 10, 13,  7,  8, 15,  9, 12,  5,  6,  3,  0, 14},
        {11,  8, 12,  7,  1, 14,  2, 13,  6, 15,  0,  9, 10,  4,  5,  3}
    },
    // S6
    {
        {12,  1, 10, 15,  9,  2,  6,  8,  0, 13,  3,  4, 14,  7,  5, 11},
        {10, 15,  4,  2,  7, 12,  9,  5,  6,  1, 13, 14,  0, 11,  3,  8},
        { 9, 14, 15,  5,  2,  8, 12,  3,  7,  0,  4, 10,  1, 13, 11,  6},
        { 4,  3,  2, 12,  9,  5, 15, 10, 11, 14,  1,  7,  6,  0,  8, 13}
    },
    // S7
    {
        { 4, 11,  2, 14, 15,  0,  8, 13,  3, 12,  9,  7,  5, 10,  6,  1},
        {13,  0, 11,  7,  4,  9,  1, 10, 14,  3,  5, 12,  2, 15,  8,  6},
        { 1,  4, 11, 13, 12,  3,  7, 14, 10, 15,  6,  8,  0,  5,  9,  2},
        { 6, 11, 13,  8,  1,  4, 10,  7,  9,  5,  0, 15, 14,  2,  3, 12}
    },
    // S8
    {
        {13,  2,  8,  4,  6, 15, 11,  1, 10,  9,  3, 14,  5,  0, 12,  7},
        { 1, 15, 13,  8, 10,  3,  7,  4, 12,  5,  6, 11,  0, 14,  9,  2},
        { 7, 11,  4,  1,  9, 12, 14,  2,  0,  6, 10, 13, 15,  3,  5,  8},
        { 2,  1, 14,  7,  4, 10,  8, 13, 15, 12,  9,  0,  3,  5,  6, 11}
    }
};

// ============================================================
//  HELPER FUNCTIONS  (provided by instructor)
// ============================================================

// Convert a hex string to a binary string
std::string hexToBinary(const std::string& hex) {
    std::string binary;
    for (char c : hex) {
        int val = 0;
        if (c >= '0' && c <= '9')      val = c - '0';
        else if (c >= 'A' && c <= 'F') val = c - 'A' + 10;
        else if (c >= 'a' && c <= 'f') val = c - 'a' + 10;
        binary += std::bitset<4>(val).to_string();
    }
    return binary;
}

// Convert a binary string to a hex string
std::string binaryToHex(const std::string& binary) {
    std::string hex;
    for (size_t i = 0; i + 4 <= binary.size(); i += 4) {
        std::bitset<4> bits(binary.substr(i, 4));
        int val = static_cast<int>(bits.to_ulong());
        std::ostringstream oss;
        oss << std::uppercase << std::hex << val;
        hex += oss.str();
    }
    return hex;
}

// Apply a permutation table to a binary string
std::string permute(const std::string& input, const int* table, int tableSize) {
    std::string output(tableSize, '0');
    for (int i = 0; i < tableSize; ++i)
        output[i] = input[table[i] - 1];
    return output;
}

// XOR two equal-length binary strings bit by bit.
std::string xorStrings(const std::string& a, const std::string& b) {
    std::string result(a.size(), '0');
    for (size_t i = 0; i < a.size(); ++i)
        result[i] = ((a[i] - '0') ^ (b[i] - '0')) ? '1' : '0';
    return result;
}

// Perform a left circular shift on a binary string by 'shifts' positions.
std::string leftShift(const std::string& bits, int shifts) {
    return bits.substr(shifts) + bits.substr(0, shifts);
}

// ============================================================
//  KEY SCHEDULE
//  Generates all 16 round keys from the 64-bit DES key.
//  DES keys are 64 bits but only 56 are used — 8 parity bits are dropped by PC-1
//  Each round key is then 48 bits, derived by left-shifting and applying PC-2
// ============================================================
std::vector<std::string> generateRoundKeys(const std::string& key) {
    std::vector<std::string> roundKeys;

    // Convert hex key to binary and apply PC-1 to drop parity bits (64 -> 56 bits)
    std::string keyBin = hexToBinary(key);
    std::string permuted = permute(keyBin, PC1, 56);

    // Split into two 28-bit halves C and D
    std::string C = permuted.substr(0, 28);
    std::string D = permuted.substr(28, 28);

    for (int round = 0; round < 16; round++) {
        // Left-shift both halves by the round-dependent amount from SHIFT_TABLE.
        C = leftShift(C, SHIFT_TABLE[round]);
        D = leftShift(D, SHIFT_TABLE[round]);

        // Concatenate C and D, then apply PC-2 to select 48 of the 56 bits as the round key — a different 48-bit subset is chosen each round
        std::string CD = C + D;
        roundKeys.push_back(permute(CD, PC2, 48));
    }

    return roundKeys;
}

// ============================================================
//  FEISTEL FUNCTION
//  The core of DES — applied to the 32-bit right half each round.
//  Takes the right half and the current round key, returns a 32-bit result
//  that gets XORed with the left half to produce the new right half.
//
//  Steps: Expansion -> XOR with round key -> S-box substitution -> P permutation
// ============================================================
std::string feistelFunction(const std::string& rightHalf,
                             const std::string& roundKey) {
    // Expand the 32-bit right half to 48 bits so it matches the round key width.
    // Some bits are repeated in the expansion — this is intentional in DES design.
    std::string expanded = permute(rightHalf, E, 48);

    // XOR the expanded block with the 48-bit round key.
    // This is where the key material enters the Feistel function.
    std::string xored = xorStrings(expanded, roundKey);

    // S-box substitution: split the 48-bit result into eight 6-bit groups
    // and pass each through its corresponding S-box to get a 4-bit output.
    // This is the only non-linear step in DES — it provides confusion.
    std::string sboxOutput = "";
    for (int i = 0; i < 8; i++) {
        std::string block = xored.substr(i * 6, 6);

        // Row is formed by the first and last bits (2-bit value, range 0-3)
        int row = 2 * (block[0] - '0') + (block[5] - '0');

        // Column is formed by the middle four bits (4-bit value, range 0-15)
        int col = 8 * (block[1] - '0') + 4 * (block[2] - '0')
                + 2 * (block[3] - '0') +     (block[4] - '0');

        int val = SBOX[i][row][col];
        sboxOutput += std::bitset<4>(val).to_string();
    }

    // Apply permutation P to the 32-bit S-box output.
    // Spreads each S-box's output across multiple positions to ensure
    // one S-box's output affects multiple S-boxes in the next round.
    return permute(sboxOutput, P, 32);
}

// ============================================================
//  DES ENCRYPTION
//  Encrypts a 64-bit plaintext block using the 64-bit key.
//  Both input and output are 16-character hex strings.
//
//  Structure:
//    Initial Permutation -> 16 Feistel rounds -> swap halves -> Final Permutation
// ============================================================
std::string desEncrypt(const std::string& plaintext,
                       const std::string& key) {
    std::vector<std::string> roundKeys = generateRoundKeys(key);

    // Convert plaintext to binary and apply the Initial Permutation
    std::string plaintextBin = hexToBinary(plaintext);
    std::string permuted = permute(plaintextBin, IP, 64);

    // Split into 32-bit left and right halves
    std::string L = permuted.substr(0, 32);
    std::string R = permuted.substr(32, 32);

    // 16 Feistel rounds — each round the halves swap and the new right half is produced by XORing the old left half with the Feistel function output
    for (int round = 0; round < 16; round++) {
        std::string newL = R;
        std::string newR = xorStrings(L, feistelFunction(R, roundKeys[round]));
        L = newL;
        R = newR;
    }

    // Swap the final halves (R16 + L16) before applying the Final Permutation.
    std::string combined = R + L;
    std::string result = permute(combined, FP, 64);

    return binaryToHex(result);
}

// ============================================================
//  DES DECRYPTION
//  Identical to encryption except round keys are applied in reverse order.
// ============================================================
std::string desDecrypt(const std::string& ciphertext,
                       const std::string& key) {
    std::vector<std::string> roundKeys = generateRoundKeys(key);

    // Reverse the round keys — roundKeys[15] is used first, roundKeys[0] last
    std::reverse(roundKeys.begin(), roundKeys.end());

    std::string ciphertextBin = hexToBinary(ciphertext);
    std::string permuted = permute(ciphertextBin, IP, 64);

    std::string L = permuted.substr(0, 32);
    std::string R = permuted.substr(32, 32);

    for (int round = 0; round < 16; round++) {
        std::string newL = R;
        std::string newR = xorStrings(L, feistelFunction(R, roundKeys[round]));
        L = newL;
        R = newR;
    }

    std::string combined = R + L;
    std::string result = permute(combined, FP, 64);

    return binaryToHex(result);
}

// ============================================================
//  MAIN — sample driver
// ============================================================
int main() {
    std::string plaintext = "123456ABCD132536";
    std::string key       = "AABB09182736CCDD";

    std::cout << "===== DES Encryption/Decryption =====\n";
    std::cout << "Plaintext : " << plaintext << "\n";
    std::cout << "Key       : " << key       << "\n";

    std::string ciphertext = desEncrypt(plaintext, key);
    std::cout << "Ciphertext: " << ciphertext << "\n";

    std::string recovered = desDecrypt(ciphertext, key);
    std::cout << "Recovered : " << recovered  << "\n";

    return 0;
}