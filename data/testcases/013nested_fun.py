# This function tests how variable capture works across multiple function
# calls.  Function 'cal1' captures 'x'.  Function 'cal2' captures 'x' and 'y'.

def cal(x : int):
  def cal1(y : int):
    def cal2(z : int):
      return x + y + z
    return cal2

  return cal1(100)(49)

export ccall cal : int -> int;
