class Switch
{
    var state:bool;
    constructor ()
        ensures this.state == false
    {
        this.state := false;
    }
    method toggle() returns (currentState : bool)
        modifies this
        ensures this.state != old(this.state)
        ensures currentState == this.state
    {
        this.state := ! this.state;
        currentState:= this.state;
    }

    method getState() returns (currentState : bool)
        ensures currentState == this.state
        ensures this.state ==  old(this.state)
    {
        currentState := this.state;
    }
}

method Test()
{
    var s := new Switch();
    var state := s.getState();
    assert(state == false);
    state := s.toggle();
    assert(state == true);
    state := s.toggle();
    assert(state == false);
    state := s.toggle();
    assert(state == true);
    state := s.toggle();
    assert(state == false);
}