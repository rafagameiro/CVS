/**
    This method goes through an array 'a' with 'n' elements to find the position
    that has the element 'e'. If the array doesn't find the position, it will return 
    the bitwise complement index of the first value in the array that is bigger than 'e'.

    This method must initially have a sorted array, and value of 'n' must be between 
    0 and the total length of the 'a'. The loop must ensure that during the iterations,
    the min and max value are always between 0 and 'n', min is always less or equals 
    than max. Also, for all possible 'k' values between 0 and 'n', the corresponding 
    value in the array 'a' at position 'k' must be different than 'e'. If k is bigger 
    or equal to max, the value is bigger than 'e', but if k is lesser than min, 
    the value at position k is lesser than 'e'.

    Finally the method ensures that if the value of z is bigger or equal to 0, it means 
    that the array 'a' has a position z whose value is equal to 'e', and therefore z 
    must be lesser than 'n'. If the value of z is lesser than 0, it means that for 
    k values between 0 and 'n', the value in the array 'a' at position k is always 
    different than 'e'. The same applies on the contrary.
    Also, if the value of z is lesser than 0, applying the bitwise operation we should 
    be able to get or a position in the array to where the element should be insert, 
    in case that's what the user desires, or a position outside of the array bounds.
    That means the element is bigger than any other value and therefore it must be 
    inserted at the end of the array, if the user ever pretends to do it.
 */
function sortedArray(a: array<int>, n: int) : bool
    requires 0 <= n <= a.Length
    reads a
{
    forall i , k :: 0 <= i <= k < n ==> a[i] <= a[k]
}

function method bitwise(pos: int) : int
{
    -(pos + 1)
}

method binarySearch(a:array<int>, n:int, e:int) returns (z:int)
    requires 0 <= n <= a.Length
    requires sortedArray(a, n)
    ensures sortedArray(a, n)
    ensures z >= 0 ==> z < n && a[z] == e 
    ensures z < 0 <==> forall k :: 0 <= k < n ==> a[k] != e 
    ensures z < 0 && 0 <= bitwise(z) < n ==> a[bitwise(z)] > e
    ensures z < 0 && bitwise(z) > n && n < a.Length ==> a[n] < e
    ensures z < 0 && bitwise(z) < 0 ==> a[0] > e
{
    var min, max := 0, n;

    while min < max
        decreases max - min
        invariant 0 <= min <= max <= n
        invariant forall k :: 0 <= k < n && max <= k ==> a[k] > e 
        invariant forall k :: 0 <= k < n && k < min ==> a[k] < e 
    {
        var mid := min + (max - min) / 2;
        if a[mid] > e
        {
            max := mid;
        } else if a[mid] < e {
            min := mid + 1;
        } else {
            return mid;       
        }
    }

    return bitwise(min);
}