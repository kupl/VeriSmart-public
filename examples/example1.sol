/* All arithmetic operations are safe from integer over/underflows. */

contract Example {

  mapping (address => uint) public balance;
  mapping (address => mapping (address => uint)) allowed;
  uint public totalSupply;

  constructor () public {
    totalSupply = 10000;
    balance[msg.sender] = 10000;
  }

  function transfer (address _to, uint _value) public returns (bool success) {
    require (balance[msg.sender] >= _value);
    balance[msg.sender] -= _value; // safe - underflow
    balance[_to] += _value; // safe - overflow
    return true;
  }

  function approve (address _spender, uint _value) public returns (bool success) {
    allowed[msg.sender][_spender] = _value;
    return true;
  }

  function transferFrom (address _from, address _to, uint _value) public returns (bool success) {
    require (balance[_from] >= _value && allowed[_from][msg.sender] >= _value);
    balance[_to] += _value; // safe - overflow
    balance[_from] -= _value; // safe - underflow
    allowed[_from][msg.sender] -= _value; // safe - underflow
    return true;
  }
}
