import argparse
from ecc.scripts.hsiao_secded import hsiao_secded_code


def main():
    parser = argparse.ArgumentParser(description="Error Correction Code Generator")
    parser.add_argument(
        "--scheme",
        type=str,
        choices=["hsiao_secded"],
        required=True,
        help="The error correction code scheme to use (e.g., hsiao_secded)",
    )
    parser.add_argument(
        "--k", type=int, required=True, help="The number of data bits (k)"
    )

    args = parser.parse_args()

    if args.scheme == "hsiao_secded":
        r, n, H, G = hsiao_secded_code(args.k)
        print(f"Number of data bits (k): {args.k}")
        print(f"Number of parity bits (r): {r}")
        print(f"Total number of bits (n): {n}\n")
        print("Parity-Check Matrix H:")
        print(H)
        print("\nGenerator Matrix G:")
        print(G)


if __name__ == "__main__":
    main()
