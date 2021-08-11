contract Example {
    address owner;

    constructor () {
        owner = msg.sender;
    }

    modifier onlyOwner {
        require (msg.sender == owner);
        _;
    }

    function setOwner (address newOwner) public {
        owner = newOwner; 
    }

    function () external payable {
    }

    function exploit (address attacker) public onlyOwner {
        attacker.transfer (address(this).balance);
    }
}
