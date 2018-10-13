class {:autocontracts} Score
{
    var highScore: int;
    predicate Valid()
    {
        this.highScore >= 0
    }


    constructor()
        ensures this.highScore == 0;
    {
        this.highScore := 0;
    }

    method NewScore(score:int) returns ( changed:bool, current: int)
        // basic change logic 
        ensures this.highScore >= old(this.highScore)
        ensures changed <==> this.highScore > old(this.highScore);
        ensures score == old(score)
        ensures score > old(this.highScore) <==> changed
        // basic return changed logic 
        ensures changed  ==> (this.highScore == score ) 
        ensures ! changed ==> this.highScore == old(this.highScore)
        // basic current value logic
        ensures changed ==> current == this.highScore == score
        ensures !changed ==> current == this.highScore

    {
        changed:= false;
        if(score > this.highScore) {
            this.highScore := score;
            changed := true;
        }
        current := this.highScore;
    }

} // end of QueueEnd class

method TestScore()
{
    var changed, current;
    var s := new Score();
    changed, current := s.NewScore(0);
    assert(changed == false);
    assert(current == 0);
    changed, current := s.NewScore(2);
    assert(changed == true);
    assert(current == 2);
    changed, current := s.NewScore(0);
    assert(changed == false);
    assert(current == 2);
    changed, current := s.NewScore(4);
    assert(changed == true);
    assert(current == 4);
    changed, current := s.NewScore(4);
    assert(changed == false);
    assert(current == 4);
    changed, current := s.NewScore(6);
    assert(changed == true);
    assert(current == 6);
}