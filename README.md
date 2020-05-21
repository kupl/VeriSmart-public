# VeriSmart
VeriSmart is a safety verifier for Solidity smart contracts.
A key feature of VeriSmart is automatically inferring transcation invariants,
conditions that hold under arbitrary interleaving of transcations, of smart contracts. 
With this ability, VeriSmart can precisely analyze safety properties (e.g., no integer overflows) in smart contracts.

VeriSmart is developed by [Software Analysis Laboratory](http://prl.korea.ac.kr/~pronto/home/) at Korea University.

The benchmarks used to evaluate the effectiveness of VeriSmart in our [paper](https://www.computer.org/csdl/proceedings-article/sp/2020/349700a825/1j2LfVGEWre) are available [here](https://github.com/kupl/VeriSmart-benchmarks).

## Installation
### Dependencies
- Install OCaml libraries below:
```
opam install -y conf-m4.1 ocamlfind ocamlbuild num yojson batteries ocamlgraph
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
./main.native -input CONTRACT.sol -root ROOTNAME
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

## Related Publications
For technical details of VeriSmart, please see our papers below.

* **VeriSmart: A Highly Precise Safety Verifier for Ethereum Smart Contracts** <br/>
  [Sunbeom So](https://sites.google.com/site/sunbeomsoprl/), Myungho Lee, Jisu Park, Heejo Lee, and [Hakjoo Oh](http://prl.korea.ac.kr/~pronto/home/) <br/>
  [S&P2020: 41st IEEE Symposium on Security and Privacy](https://www.ieee-security.org/TC/SP2020/) <br/>
  \[[paper link](https://www.computer.org/csdl/proceedings-article/sp/2020/349700a825/1j2LfVGEWre)\] \[[benchmarks](https://github.com/kupl/VeriSmart-benchmarks)\] \[[video abstract](https://www.youtube.com/watch?v=OIqjKqVm-F4)\]

## Contact
[Sunbeom So](https://sites.google.com/site/sunbeomsoprl/): sunbeom_so@korea.ac.kr
