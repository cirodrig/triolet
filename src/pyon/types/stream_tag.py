
import pyon.unification as unification

class StreamTag(unification.Unifiable, object):
    "A tag indicating whether a variable should be passed as a stream."
    pass

class IsStream(StreamTag, unification.Term):
    def __new__(cls):
        x = IsStream._singleton
        if not x:
            x = IsStream._singleton = super(cls, IsStream).__new__(cls)
        return x

    _singleton = None

    def __init__(self):
        # Do nothing
        pass

    def __eq__(self, other): return self is other

    # Pun self as constructor
    def getConstructor(self): return self

    def getParameters(self): return []

    def rename(self, s): return self

    def pretty(self):
        return "stream"

class IsAction(StreamTag, unification.Term):
    def __new__(cls):
        x = IsAction._singleton
        if not x:
            x = IsAction._singleton = super(cls, IsAction).__new__(cls)
        return x

    _singleton = None

    def __init__(self):
        # Do nothing
        pass

    def __eq__(self, other): return self is other

    # Pun self as constructor
    def getConstructor(self): return self
    
    def getParameters(self): return []

    def rename(self, s): return self

    def pretty(self):
        return "action"

class StreamTagVar(StreamTag, unification.Variable):
    def __init__(self):
        unification.Variable.__init__(self)

    def pretty(self):
        return "t" + hex(id(self))[2:]
