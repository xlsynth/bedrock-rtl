# Copyright 2024 The Bedrock-RTL Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""
Hsiao SECDED code generator

References:
[1] https://ieeexplore.ieee.org/abstract/document/5391627
[2] https://arxiv.org/pdf/0803.1217

"""

import numpy as np
import math
import argparse


def get_r(k: int) -> int:
    """Calculate the number of parity bits (p) required for a Hsiao SECDED code with the given message length (k) in bits."""
    r = 1
    while r < math.ceil(math.log2(k + r)) + 1:
        r += 1
    return r


def get_n(k: int, r: int) -> int:
    """Calculate the total number of bits in a codeword (n) for a Hsiao SECDED code with the given message length (k) and parity length (p) in bits."""
    return k + r


def get_k(n: int, r: int) -> int:
    """Calculate the number of message bits (k) in a codeword for a Hsiao SECDED code with the given codeword length (n) and parity length (p) in bits."""
    return n - r


def uint_to_bit_vector(number: int, bit_length: int) -> list:
    """Convert an unsigned integer to a vector of bits with a specified length."""
    if number < 0:
        raise ValueError("Number must be non-negative.")
    binary_str = format(number, f"0{bit_length}b")
    bit_vector = [int(bit) for bit in binary_str]
    return bit_vector


def min_column_weight(k: int, r: int) -> int:
    """Returns the smallest odd column weight that can be used to construct the r x k message part of the parity-check matrix."""
    for weight in range(3, r, 2):
        num_ways = math.comb(r, weight)
        if num_ways >= k:
            return weight
    raise ValueError("No valid column weight found!")


def parity_check_message_columns(r: int, k: int, col_weight: int) -> np.ndarray:
    """Returns a set of parity columns for the r x k message part of the r x n parity-check matrix."""
    # This is not the most efficient way of finding the columns, but it works!
    ret = np.zeros((r, k), dtype=int)
    i = 0
    c = 0
    while c < k:
        vec = uint_to_bit_vector(i, r)
        if sum(vec) == col_weight:
            assert (sum(vec) % 2) == 1
            ret[:, c] = vec
            c += 1
        i += 1
    assert check_columns_unique(ret)
    return ret


def check_columns_unique(matrix: np.ndarray) -> bool:
    """Check that no columns are the same in the given matrix."""
    for ci in range(matrix.shape[1]):
        for cj in range(ci + 1, matrix.shape[1]):
            assert not np.array_equal(matrix[:, ci], matrix[:, cj])
    return True


def get_H(k: int, r: int) -> np.ndarray:
    """Generate the n x r parity-check matrix H for a Hsiao SECDED code with the given number of parity bits.

    Reference [2] states:
    > The definition of Hsiao code is a type of SEC-DED codes whose check matrix H defined on GF(2)
    > satisfies:
    > (1) Every column contains an odd number of 1s.
    > (2) The total number of 1s reaches the minimum.
    > (3) The difference of the number of 1s in any two rows is not greater than 1.
    > (4) No two columns are the same.
    """
    n = get_n(k, r)
    # Fill H_m with column vectors that satisfy conditions (1), (2), and (4).
    min_msg_col_weight = min_column_weight(k, r)
    H_m = parity_check_message_columns(r, k, min_msg_col_weight)
    # r x r matrix for parity bits (identity)
    H_p = np.identity(r, dtype=int)
    H = np.hstack((H_m, H_p))  # Combine message and parity parts in systematic form
    return H


def get_G(H: np.ndarray) -> np.ndarray:
    """Generate the k x n generator matrix G for a Hsiao SECDED code with the given r x n parity-check matrix H."""
    r = H.shape[0]
    n = H.shape[1]
    k = get_k(n, r)
    # Message part of G is identity matrix since we want systematic form.
    G_m = np.identity(k, dtype=int)
    H_m = H[:, :k]
    # Parity part of G is the transpose of the messsage part of H.
    G_p = H_m.T
    G = np.hstack((G_m, G_p))
    return G


def hsiao_secded_code(k: int) -> tuple[int, int, np.ndarray, np.ndarray]:
    """Generate a Hsiao SECDED code with the given number of message bits.

    Args:
        k: Number of message bits (k)

    Returns:
        tuple[int, int, np.ndarray, np.ndarray]:
            - Number of parity bits (r)
            - Number of codeword bits (n)
            - Parity-check matrix (H) of shape r x n
            - Generator matrix (G) of shape k x n
        Such that c = m * G and s = H * c^T, where:
            - m is the 1 x k message
            - c is the 1 x n codeword
            - s is the r x 1 syndrome
    """
    r = get_r(k)
    n = get_n(k, r)
    print(f"Number of message bits (k): {k}")
    print(f"Number of parity bits (r): {r}")
    print(f"Number of codeword bits (n): {n}")
    print("Constructing parity-check matrix H.")
    H = get_H(k, r)
    print("Constructing generator matrix G.")
    G = get_G(H)
    print("Parity-Check Matrix H:")
    print(H)
    print("Generator Matrix G:")
    print(G)
    return r, n, H, G


def main():
    parser = argparse.ArgumentParser(description="Hsiao SECDED code generator.")
    parser.add_argument("k", type=int, help="Number of data bits (k)")
    args = parser.parse_args()
    hsiao_secded_code(args.k)


if __name__ == "__main__":
    main()