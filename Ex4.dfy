// define the color of the flag 
datatype Colour = RED | BLUE | YELLOW | GREEN 

method FlagSort(flag:array<Colour>) 
    modifies flag;
    // provide two valid index 
    ensures forall x::  0 < x < flag.Length ==> 
        (flag[x] == RED ==> flag[x-1] == RED) 
    ensures forall x::  0 < x < flag.Length ==> 
        (flag[x] == BLUE ==> 
            (flag[x-1] == BLUE || flag[x-1] == RED )) 
    ensures forall x::  0 < x < flag.Length ==> 
        (flag[x] == YELLOW ==> 
            (
                flag[x-1] == BLUE || 
                flag[x-1] == RED  ||
                flag[x-1] == YELLOW 
            )
        ) 
    ensures forall x::  0 < x < flag.Length ==> 
        (flag[x] == GREEN ==> (
            flag[x-1] == BLUE   ||
            flag[x-1] == RED    || 
            flag[x-1] == YELLOW || 
            flag[x-1] == GREEN
        )) 

{
    var next := 0;
    var blue := 0;
    // colours between next and yellow unsorted
    var yellow := flag.Length; 
    var green := flag.Length; 
    while (next != yellow) // when next==blue, no colours left to sort
        decreases yellow + green - next
        invariant 0 <= blue <= next <= yellow <= green <= flag.Length
        invariant forall x:: 0      <= x < blue        ==> flag[x] == RED
        invariant forall x:: blue   <= x < next        ==> flag[x] == BLUE
        invariant forall x:: yellow <= x < green       ==> flag[x] == YELLOW
        invariant forall x:: green  <= x < flag.Length ==> flag[x] == GREEN
    {
        match (flag[next])
        {
            case BLUE => 
                next := next + 1; 
            case RED => 
                // swap to the blue's start 
                flag[blue], flag[next] := flag[next], flag[blue];
                blue := blue + 1;
                next := next + 1;
            case YELLOW => 
                yellow := yellow -1;
                // append at the Yellow region by swap 
                // hence next now will have an unsortedc item 
                flag[yellow] , flag[next] := flag[next], flag[yellow];
            case GREEN => 
                green := green -1;
                yellow := yellow -1;
                flag[green] , flag[next] := flag[next], flag[green];
                if ( yellow != green){
                    // this must a yellow in next 
                    flag[next], flag[yellow]:= flag[yellow],flag[next];
                }

        }
    }
}