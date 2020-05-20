contract Example {

  mapping (address => uint) public balance;
  mapping (address => mapping (address => uint)) allowed;
  uint public totalSupply;

  address public owner;

  constructor () public {
    totalSupply = 10000;
    balance[msg.sender] = 10000;
    owner = msg.sender;
  }

  modifier onlyOwner {
    require (msg.sender == owner);
    _;
  }

  function mintToken (address _target, uint _amount) onlyOwner public {
    balance[_target] += _amount; // unsafe - overflow
    totalSupply += _amount; // unsafe - overflow
  }

  function transfer (address _to, uint _value) public returns (bool success) {
    require (balance[msg.sender] >= _value);
    balance[msg.sender] -= _value; // safe - underflow
    balance[_to] += _value; // unsafe - overflow
    return true;
  }

  function approve (address _spender, uint _value) public returns (bool success) {
    allowed[msg.sender][_spender] = _value;
    return true;
  }

  function transferFrom (address _from, address _to, uint _value) public returns (bool success) {
    require (balance[_from] >= _value && allowed[_from][msg.sender] >= _value);
    balance[_to] += _value; // unsafe - overflow
    balance[_from] -= _value; // unsafe - underflow: self-transfer case
    allowed[_from][msg.sender] -= _value; // safe - underflow
    return true;
  }
}
