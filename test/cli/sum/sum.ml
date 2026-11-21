let rec sum n = if n <= 0 then 0 else n + sum (n - 1)
(*@ r = sum n
    requires n >= 0
    ensures r >= 0 && r >= n *)

;; sum 10
