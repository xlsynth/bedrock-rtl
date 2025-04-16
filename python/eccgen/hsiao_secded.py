# Copyright 2024-2025 The Bedrock-RTL Authors
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
import textwrap
from itertools import combinations


def get_r(k: int) -> int:
    """Calculate the number of parity bits r for a Hsiao SECDED code with k message bits."""
    r = 1
    while r < math.ceil(math.log2(k + r)) + 1:
        r += 1
    return r


def _balanced_message_matrix_greedy(r: int, k: int) -> np.ndarray:
    """
    Build the r x k message-part Hm by greedy selection of the lowest-weight
    odd columns to minimize row-sum imbalance.
    """
    # Generate all odd-weight column candidates (weight 3,5,...)
    candidates: list[np.ndarray] = []
    for J in range(3, r + 1, 2):
        for combo in combinations(range(r - 1, -1, -1), J):
            col = np.zeros(r, dtype=int)
            col[list(combo)] = 1
            candidates.append(col)
    used = [False] * len(candidates)
    row_sums = np.zeros(r, dtype=int)
    selected_cols: list[np.ndarray] = []

    for _ in range(k):
        best_i = None
        best_diff = None
        best_min = None
        # pick the column that yields minimal (max-min) row_sum difference,
        # breaking ties by largest minimum row sum
        for i, col in enumerate(candidates):
            if used[i]:
                continue
            new_sums = row_sums + col
            diff = int(new_sums.max() - new_sums.min())
            mn = int(new_sums.min())
            if (
                best_i is None
                or diff < best_diff
                or (diff == best_diff and mn > best_min)
            ):
                best_i, best_diff, best_min = i, diff, mn
        used[best_i] = True
        selected_cols.append(candidates[best_i].reshape(r, 1))
        row_sums += candidates[best_i]
    Hm = np.hstack(selected_cols)
    return Hm


def get_H(k: int, r: int) -> np.ndarray:
    """Generate the r x n parity-check matrix H for a Hsiao SECDED code."""
    # Build a perfectly row-balanced message matrix of k odd-weight columns
    Hm = _balanced_message_matrix_greedy(r, k)
    # Append parity-bit identity
    Hp = np.eye(r, dtype=int)
    H = np.hstack((Hm, Hp))
    return H


def get_G(H: np.ndarray) -> np.ndarray:
    """Generate the k x n generator matrix G for a Hsiao SECDED code with the given r x n parity-check matrix H."""
    r = H.shape[0]
    n = H.shape[1]
    k = n - r
    # Message part of G is identity matrix since we want systematic form.
    G_m = np.identity(k, dtype=int)
    H_m = H[:, :k]
    # Parity part of G is the transpose of the messsage part of H.
    G_p = H_m.T
    G = np.hstack((G_m, G_p))
    return G


def binary_matmul(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    """Multiply two binary matrices (A @ B) and raise a ValueError if the result is not binary."""
    AB = (A @ B) % 2
    return AB


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
    if k <= 0:
        raise ValueError("k must be positive.")
    r = get_r(k)
    n = k + r
    H = get_H(k, r)
    G = get_G(H)
    return r, n, H, G


def encode(m: np.ndarray, G: np.ndarray) -> np.ndarray:
    """Encode a message m using the generator matrix G."""
    return binary_matmul(m, G)


def decode_syndrome(c: np.ndarray, H: np.ndarray, k: int) -> np.ndarray:
    """Decode a codeword c to a syndrome using the parity-check matrix H."""
    return binary_matmul(c, H.T)


def decode_message(
    c: np.ndarray, s: np.ndarray, H: np.ndarray
) -> tuple[np.ndarray, bool, bool]:
    """Decode a codeword c to a message using the syndrome s.

    Args:
        c: Codeword of shape (n,)
        s: Syndrome of shape (r,)
        H: Parity-check matrix of shape (r, n)

    Returns:
        tuple[np.ndarray, bool, bool]:
            - Decoded message. Can be valid only if no double-bit error was detected.
            - True if a single-bit error was corrected, False otherwise
            - True if a double-bit error was detected-but-uncorrectable, False otherwise
    """
    n = c.shape[0]
    r = s.shape[0]
    k = n - r
    if H.shape[0] != r or H.shape[1] != n:
        raise ValueError("H must be r x n.")

    # Case 0: Syndrome is zero, no errors detected.
    if np.all(s == 0):
        return (c[:k], False, False)

    # Case 1: Syndrome is for an even number of bits in error, which happens when the syndrome is even in a Hsiao SECDED code.
    # Maximum likelihood decoding produces multiple equiprobable candidate codewords, so treat as detected-but-uncorrectable.
    # NOTE: We are returning *some* message but it is likely to have been corrupted!
    if (np.sum(s) % 2) == 0:
        return (c[:k], False, True)

    # Remaining case: Syndrome is for an odd number of bits in error, which happens when the syndrome is odd in a Hsiao SECDED code.
    # *Usually* this is a single-bit error, which is always closest to exactly one codeword. So with maximum likelihood decoding
    # we can correct it. However, sometimes it can be a three-bit error that is actually detected-but-uncorrectable.
    assert np.sum(s) % 2 == 1
    for ci in range(n):
        # If the syndrome equals a column of H, then we decide the error is in that column and we can correct it.
        if np.array_equal(H[:, ci], s):
            loc = ci
            c[loc] = 1 - c[loc]
            return (c[:k], True, False)

    # If no column of H matches the syndrome, then the codeword is uncorrectable.
    # Similarly to above, we return *some* message but it is likely to have been corrupted!
    return (c[:k], False, True)


def G_col_to_sv(col: np.ndarray, col_idx: int) -> str:
    """Generate a Verilog RTL assignment for a single column of the generator matrix G."""
    xors = []
    nonzero_indices = np.nonzero(col)[0]
    for i in nonzero_indices:
        xors.append(f"m[{i}]")
    return f"    assign parity[{col_idx}] = " + " ^ ".join(xors) + ";"


def G_to_sv(G: np.ndarray) -> str:
    """Generate Verilog RTL code for the given generator matrix G."""
    assigns = []
    # Since we know G is in systematic form, we can just assign the message bits to the codeword bits.
    # We don't need to codegen that part.
    k = G.shape[0]
    r = get_r(k)
    for i in range(r):
        assigns.append(G_col_to_sv(G[:, k + i], i))
    return "\n".join(assigns)


def syndrome_bit_to_sv(row: np.ndarray, row_idx: int) -> str:
    """Generate a Verilog RTL assignment for a single bit of the syndrome."""
    xors = []
    nonzero_indices = np.nonzero(row)[0]
    for i in nonzero_indices:
        xors.append(f"cw[{i}]")
    return f"    assign syndrome[{row_idx}] = " + " ^ ".join(xors) + ";"


def syndrome_to_sv(H: np.ndarray) -> str:
    """Generate Verilog RTL code for the syndrome of the given parity-check matrix H."""
    assigns = []
    r = H.shape[0]
    for i in range(r):
        # Reverse row index (r - i - 1)  because row 0 is actually the MSb of the syndrome
        assigns.append(syndrome_bit_to_sv(H[i, :], r - i - 1))
    return "\n".join(assigns)


def H_col_to_sv(col: np.ndarray, col_idx: int) -> str:
    """Generate a Verilog RTL assignment for a single column of the parity-check matrix H."""
    r = col.shape[0]
    return (
        f"    assign parity_check_matrix[{col_idx}] = {r}'b"
        + "".join(col.astype(str))
        + ";"
    )


def H_to_sv(H: np.ndarray) -> str:
    """Generate Verilog RTL code for the columns of the given parity-check matrix H."""
    assigns = []
    for i in range(H.shape[1]):
        assigns.append(H_col_to_sv(H[:, i], i))
    return "\n".join(assigns)


def check_construction(G: np.ndarray, H: np.ndarray) -> None:
    """Raises a ValueError if the given generator matrix G and parity-check matrix H are not a valid Hsiao SECDED code."""

    def check_columns_unique(matrix: np.ndarray) -> None:
        """Raises a ValueError if any columns are the same in the given matrix."""
        for ci in range(matrix.shape[1]):
            for cj in range(ci + 1, matrix.shape[1]):
                if np.array_equal(matrix[:, ci], matrix[:, cj]):
                    raise ValueError("Columns are not unique.")

    def check_column_weights_are_odd(matrix: np.ndarray) -> None:
        """Raises a ValueError if any columns in the given matrix do not have an odd weight."""
        sum_over_rows = np.sum(matrix, axis=0)
        if not np.all(sum_over_rows % 2 == 1):
            err_string = [
                "Columns do not have an odd weight.",
                f"matrix = \n{matrix}",
                f"sums = \n{sum_over_rows}",
            ]
            raise ValueError("\n".join(err_string))

    def check_minimum_total_weight(H: np.ndarray) -> None:
        """
        Raise a ValueError if the total number of 1s in H exceeds the lower bound.
        (Hsiao codes purport to achieve the lower bound.)
        """

        def minimal_total_weight(r: int, k: int) -> int:
            """
            Calculate the minimal total number of 1s for an r x n Hsiao parity-check matrix,
            based on selecting the k odd-weight columns of smallest weight. n = r + k.
            """
            total = 0
            remaining = k
            for J in range(3, r + 1, 2):
                count = math.comb(r, J)
                take = min(count, remaining)
                total += take * J
                remaining -= take
                if remaining == 0:
                    break
            # Add on the identity matrix of parity bits (systematic form)
            total += r
            return total

        r, n = H.shape
        k = n - r
        actual = int(np.sum(H))
        minimal = minimal_total_weight(r, k)
        if actual != minimal:
            err = [
                "Total weight of H is not minimal.",
                f"actual weight = {actual}",
                f"minimal weight = {minimal}",
                f"H = \n{H}",
            ]
            raise ValueError("\n".join(err))

    def check_distance_ge_4(H: np.ndarray) -> None:
        """Raises a ValueError if the distance of the code is less than 4."""
        r, n = H.shape
        # Test every subset of 1, 2, or 3 columns
        for t in (1, 2, 3):
            for cols in combinations(range(n), t):
                sub = H[:, cols]  # shape r x t
                # over GF(2), independence means sub @ x = 0 only for x=0
                # but with t<=r we can check rank = t:
                if np.linalg.matrix_rank(sub % 2) < t:
                    err_string = [
                        "Columns are dependent -> distance < 4.",
                        f"columns = {cols}",
                        f"matrix = \n{matrix}",
                    ]
                    raise ValueError("\n".join(err_string))

    def check_row_sums_differ_by_at_most_one(matrix: np.ndarray) -> None:
        """Raises a ValueError if the row sums of the given matrix differ by more than one."""
        sum_over_columns = np.sum(matrix, axis=1)
        if not np.all(np.abs(sum_over_columns - sum_over_columns[0]) <= 1):
            err_string = [
                "Row sums differ by more than one.",
                f"matrix = \n{matrix}",
                f"row sums = \n{sum_over_columns}",
            ]
            raise ValueError("\n".join(err_string))

    def check_matrix_is_binary(matrix: np.ndarray) -> None:
        """Raises a ValueError if the given matrix is not binary (contains only 0s and 1s)."""
        zeros = matrix == 0
        ones = matrix == 1
        if not np.all(zeros + ones):
            matrix_str = np.array2string(
                matrix, separator=", ", threshold=np.inf, max_line_width=np.inf
            )
            err_string = [
                "Matrix contains non-binary values:",
                f"{matrix_str}",
            ]
            raise ValueError("\n".join(err_string))

    def check_matrices_orthogonal(A: np.ndarray, B: np.ndarray) -> None:
        """Raises a ValueError if two matrices are not orthogonal (A @ B != 0)."""
        AB = binary_matmul(A, B)
        if not np.all(AB == 0):
            A_str = np.array2string(
                A, separator=", ", threshold=np.inf, max_line_width=np.inf
            )
            B_str = np.array2string(
                B, separator=", ", threshold=np.inf, max_line_width=np.inf
            )
            AB_str = np.array2string(
                AB, separator=", ", threshold=np.inf, max_line_width=np.inf
            )
            err_string = [
                "Matrices are not orthogonal.",
                f"A =\n{A_str}",
                f"B =\n{B_str}",
                f"A @ B =\n{AB_str}",
            ]
            raise ValueError("\n".join(err_string))

    def check_G_systematic(G: np.ndarray) -> bool:
        """Raises a ValueError if the given generator matrix G is not in systematic form."""
        k = G.shape[0]
        I_k = np.identity(k, dtype=int)
        if not np.array_equal(G[:, :k], I_k):
            raise ValueError("Generator matrix G is not in systematic form.")

    def check_H_systematic(H: np.ndarray) -> None:
        """Raises a ValueError if the given parity-check matrix H is not in systematic form."""
        r, n = H.shape
        k = n - r
        I_r = np.identity(r, dtype=int)
        if not np.array_equal(H[:, k:], I_r):
            raise ValueError("Parity-check matrix H is not in systematic form.")

    check_matrix_is_binary(G)
    check_matrix_is_binary(H)
    check_columns_unique(G)
    check_columns_unique(H)
    check_column_weights_are_odd(H)
    check_row_sums_differ_by_at_most_one(H)
    check_minimum_total_weight(H)
    check_distance_ge_4(H)
    check_G_systematic(G)
    check_H_systematic(H)
    check_matrices_orthogonal(G, H.T)
