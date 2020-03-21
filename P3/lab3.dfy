/**
    ©João Costa Seco, Eduardo Geraldo, CVS, FCT NOVA, MIEI 2020
    This is the first lab assignment for the Construction and Verification of
    Software of the integrated master in computer science and engineering
    (MIEI) http://www.di.fct.unl.pt/miei


    Your mission is to complete all methods below using dafny. Completely 
    specify the methods by writing the weakest pre-condition and the strongest
    post-condition possible. Implement and verify the methods according to that
    same specification.
 */



/**
    Specify and implement the method computeDivision; this method yields a
    pair (a, b), where a is the result of the integer division of x by y 
    and b is the remainder the division.
        (a, b) == (x/y, x%y)

    In the specification define the weakest preconditions and
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
    
    The implementation of this method should be iterative.

    To return a pair use:
        <return a, b;>

    Note 1: consider as input only non-negative values

    Note 2: in the postconditions avoid using the existing division <x/y>
    and modulo <x%y> operations.
*/
method computeDivision(x:int, y:int) returns (a:int, b:int)
    requires y > 0
    ensures x == y * a + b
    ensures b < y
{
    var n := x;
    a := 0;
    while n >= y 
        decreases n - y
        invariant x == y * a + n
    {   
        a := a + 1;
        n := n - y;
    }
    b := n;

    return a, b;
}

function factorial(x: int): int 
    decreases x
    requires x >= 0
{
    if x == 0 then 1 else x * factorial( x - 1)
}

/**
    Specify and implement the method computeFactorial; this method returns
    the factorial of x, i.e.m !x. For instance, computeFactorial(3) yields
    the result 6.

    In the specification define the weakest preconditions and
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
    
    Hint: you will most likely need to define an auxilliary function.
*/
method computeFactorial(x:int) returns (z:int)
    requires x >= 0
    ensures z == factorial(x)
{

    var i := 0;
    var a := 1;

    while i < x
        decreases x - i
        invariant 0 <= i <= x
        invariant a == factorial(i)
    {
        i := i + 1;   
        a := a * i; 
    }

    return a;
}

/**
    Specify and implement the method computeFibbonaci; this method returns
    the result of the fibonacci function over the arument x.
    For example, computeFibonacci(3) == 2

    In the specification define the weakest preconditions and
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.

    See: https://en.wikipedia.org/wiki/Fibonacci_number
*/
method computeFibonacci(x:int) returns (z:int)

/**
    Specify and implement method indexOf below. The functionality of this method
    it to return the index of the first occurrence of elem in array a.

    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
*/
method indexOf(a:array<int>, n:int, elem:int) returns (z:int)
    requires 0 <= n <= a.Length
    ensures -1 <= z < n
    ensures 0 <= z < n ==> a[z] == elem 
    ensures z == -1 ==> forall k :: 0 <= k < n ==> a[k] != elem
{

    var i := 0;
    while i < n
        decreases n - i
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> a[k] != elem
    {
        if a[i] == elem
        {
            return i;
        }
        i := i + 1;
    }

    return -1;
}

/**
    Specify and implement method max. This method retuns a pair where
    the first element is the greatest value in the array and the second
    element of the pair is its index. The first argument is the array
    to search and the second one the number of elements in the array.


    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
*/
method max(a:array<int>, n:int) returns (maxVal:int, maxIdx:int)
    requires 0 < n <= a.Length
    ensures 0 <= maxIdx < n
    ensures forall k :: 0 <= k < n ==> a[k] <= maxVal
{
    var i := 1;
    var m := a[0];
    var mi := 0;

    while i < n
        decreases n - i
        invariant 1 <= i <= n
        invariant 0 <= mi < i
        invariant forall k :: 0 <= k < i ==> a[k] <= m
    {
        if a[i] > m
        {
            m := a[i];
            mi := i;
        }

        i := i + 1;
    }
    

    return m, mi;
}

/**
    Specify and implement method min. This method retuns a pair where
    the first element is the lowest value in the array and the second
    element of the pair is its index. The first argument is the array
    to search and the second one the number of elements in the array.

    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
*/
method min(a:array<int>, n:int) returns (minVal:int, minIdx:int)
    requires 0 < n <= a.Length
    ensures 0 <= minIdx < n
    ensures forall k :: 0 <= k < n ==> a[k] >= minVal
{
    var i := 1;
    var m := a[0];
    var mi := 0;

    while i < n
        decreases n - i
        invariant 1 <= i <= n
        invariant 0 <= mi < i
        invariant forall k :: 0 <= k < i ==> a[k] >= m
    {
        if a[i] < m
        {
            m := a[i];
            mi := i;
        }

        i := i + 1;
    }
    

    return m, mi;
}

/**
    Specify and implement method fillK. This method retuns true if and only
    if the first count elements of array a are equal to k.
    The first argument is the array, the second one is the number of 
    elements in the array, the third argument is the value to use as
    comparison, and the last argument is the number of times that k must
    be appear in the array.
    
    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
*/
method fillK(a:array<int>, n:int, k:int, count:int) returns (b:bool)
    requires 0 <= count < n <= a.Length
    ensures b <==> forall j :: 0 <= j < count ==> a[j] == k
{
    var i := 0;

    while i < count
        decreases count - i
        invariant 0 <= i <= count
        invariant forall j :: 0 <= j < i ==> a[j] == k
    {
        if a[i] != k
        {
            return false;
        }
        i := i + 1;
    }

    return true;
}

/**
    Specify and implement method containsSubString. This method tests wheteher or
    not the cahr array a contains the char array b. 
    If a contains b, then the method returns the offset of b on a.
    If a does not contain n then the method returns an illegal index.

    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.

    Hint: you may want to define an auxiliary function and method.
*/
method containsSubString(a:array<char>, b:array<char>) returns (pos:int)
    requires b.Length <= a.Length
{
    var i := 0;
    var n := a.Length;

    while i < n
        decreases n - i
    {
        //if a[i] 

        i := i + 1;
    }


    return -1; 
}

/**
    Specify and implement method resize. This method returns a new array
    which Length is the double of the length of the array supplied as 
    argument.

    If the length of the array supplied as argument is zero, then set the
    length of b to a constant of your choice.

    All the elements of a should be inserted, in the same order, in b.

    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
*/
method resize(a:array<int>) returns (z:array<int>)

/**
    Specify and implement method reverse. This method returns a new array b
    in which the elements of a appear in the inverse order.

    For instance the inverse of array a, a == [0, 1, 5, *, *], where '*'
    denotes an uninitialized array position, results i:
    b == [5, 1, 0, *, *].

    The first parameter is the array to reverse and the second one
    is the number of values in a.

    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
*/
method reverse(a:array<int>, n:int) returns (z:array<int>)
    requires 0 < n <= a.Length
    ensures  a.Length == z.Length
    ensures forall i :: 0 <= i < n ==> a[i] == z[n-i-1]
{
    var i := 0;
    z := new int[a.Length];

    while i < n
        decreases n - i
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> a[k] == z[n-k-1]
    {
        z[n - i -1] := a[i];
        i := i + 1;
    }

    return z;
}

/**
    Specify and implement method push.
    This method accepts three arguments, an array, the number of elements in the
    array, and the new element.

    It will insert the new element at the end of the array and return a pair
    with the modified array and the new number of elements in the array.

    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.

    Note: You will need to use a modifies clause:
        <modifies a>.
    This clause lets Dafny know that you intend to change the contents of
    array a.
*/
method push(a:array<int>, na:int, elem:int) returns (b:array<int>, nb:int)

/**
    Specify and implement method pop. Given an array and the number of
    elements in it, this method removes the last element of the array and 
    return the modifies array, the number of elements of the modified array
    and the element removed from the array.

    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
*/
method pop(a:array<int>, na:int) returns (b:array<int>, nb:int, elem:int)

/**
    Specify and implement method Count. Given an array a and some integer v, 
    this method return the number of occurrences of v in a.

    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
*/
//TODO faltam os ensures/invariants
method Count(a:array<int>, v:int) returns (z:int)
    requires true
    ensures z >= 0
{
    var i := 0;
    z := 0;
    var n := a.Length;

    while i < n
        decreases n - i
    {
        if a[i] == v
        {
            z := z + 1; 
        }

        i := i + 1;
    }

    return z;
}