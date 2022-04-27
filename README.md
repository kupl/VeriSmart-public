# VeriSmart
VeriSmart is a safety analyzer for Solidity smart contracts. Currently, VeriSmart supports two types of analysis modes.
- Safety verification (**VeriSmart**, [S&P '20](https://arxiv.org/abs/1908.11227))

In this mode, VeriSmart can be used to prove the absence of bugs or detect bugs. The key feature in this mode is, VeriSmart automatically infers transcation invariants, which are conditions that hold under arbitrary interleaving of transcations, of smart contracts. With this ability, VeriSmart can precisely analyze safety properties (e.g., no integer overflows) in smart contracts.

- Vulnerable transaction sequence generation (**SmarTest**, [Security '21](http://prl.korea.ac.kr/~ssb920/papers/sec21.pdf))

VeriSmart in this mode can be used to generate vulnerable transaction sequences (with concrete arguments for each transaction) that demonstrate the flaws. The key feature in this mode is, we guide a symbolic execution procedure with language models to find vulnerable sequences effectively. VeriSmart in this mode is called SmarTest.

VeriSmart has been developed and maintained by [Software Analysis Laboratory](http://prl.korea.ac.kr/~pronto/home/) at Korea University.

The benchmarks used in our papers ([S&P '20](https://arxiv.org/abs/1908.11227), [Security '21](http://prl.korea.ac.kr/~ssb920/papers/sec21.pdf)) are available [here](https://github.com/kupl/VeriSmart-benchmarks).

## Installation
### Dependencies
- Install OCaml libraries below:
```
opam install -y conf-m4.1 ocamlfind ocamlbuild num yojson batteries ocamlgraph zarith
```

- Install Z3:
```
wget https://github.com/Z3Prover/z3/releases/download/z3-4.7.1/z3-4.7.1.tar.gz
tar -xvzf z3-4.7.1.tar.gz
cd z3-z3-4.7.1
python3 scripts/mk_make.py --ml
cd build
make -j 4
sudo make install
```

- Install Solidity Compiler (solc).

### Build
```
Clone this project.
chmod +x build
./build
```

## Usage
You can check execution options by `./main.native -help`.
### Examples
- Set verification timeout to 1 minute with `-verify_timeout`, and set Z3 timeout (per query) to 10 seconds with `-z3timeout`.
```bash
# -verify_timeout: specified in seconds (default: 5 minutes)
# -z3timeout: specified in milliseconds (default: 30 seconds)
./main.native -input CONTRACT.sol -verify_timeout 60 -z3timeout 10000
```

- Specify a root contract with `-main`.
```
./main.native -input CONTRACT.sol -main ROOTNAME
```
Note that, if `-main` option is not provided, VeriSmart will assume the last contract in source code as a root contract.

- Specify a solc version with `-solc`.
```
./main.native -input CONTRACT.sol -solc 0.5.11
```
Note that, in this case, `CONTRACT.sol` must be compiled with solc v.0.5.11,
where the solc binary named `solc_0.5.11` should be located at the path identified by `which solc_0.5.11`.
If the `-solc` option is not explicitly provided,
VeriSmart will attempt to compile the source code with solc binary named `solc`, located at the path identified by `which solc`.

- To run SmarTest (vulnerable sequence geeneration mode), specify the mode with `-mode`.
```
./main.native -input examples/leak_unsafe.sol -mode exploit -exploit_timeout 10 leak
```
Note that the default mode is verification mode. You can also explicitly specify verification mode by providing `-mode verify` option.

- Vulnerability types to be analyzed can be specified by their names (e.g., see the above example).
  * io (integer over/underflow), dz (division-by-zero), assert (assertion violation), leak (ether-leaking), kill (suicidal), re (reentrancy, only verification mode), tx (tx.origin, only verification mode), erc20 (erc20 violation, only exploit mode)

- You can check the full list of availble options by: `./main.native --help`

## Related Publications
For technical details of VeriSmart and SmarTest, please see our papers below.

* **VeriSmart: A Highly Precise Safety Verifier for Ethereum Smart Contracts** <br/>
  [Sunbeom So](https://sites.google.com/site/sunbeomsoprl/), Myungho Lee, Jisu Park, Heejo Lee, and [Hakjoo Oh](http://prl.korea.ac.kr/~pronto/home/) <br/>
  [S&P2020: 41st IEEE Symposium on Security and Privacy](https://www.ieee-security.org/TC/SP2020/) <br/>
  \[[paper](https://arxiv.org/abs/1908.11227)\] \[[video abstract](https://www.youtube.com/watch?v=OIqjKqVm-F4)\]

* **SmarTest: Effectively Hunting Vulnerable Transaction Sequences in Smart Contracts through Language Model-Guided Symbolic Execution** <br/>
  [Sunbeom So](https://sites.google.com/site/sunbeomsoprl/), [Seongjoon Hong](http://prl.korea.ac.kr/~june/), and [Hakjoo Oh](http://prl.korea.ac.kr/~pronto/home/) <br/>
  [Security 2021: 30th USENIX Security Symposium](https://www.usenix.org/conference/usenixsecurity21) <br/>
  \[[paper](http://prl.korea.ac.kr/~ssb920/papers/sec21.pdf)\]

## Contact
[Sunbeom So](https://sites.google.com/site/sunbeomsoprl/): sunbeom_so@korea.ac.kr
