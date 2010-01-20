"""Pretty-printing routines.

These functions produce documents that can be formatted and written to
a file by 'prettyPrint'.  The documents manage indentation and spacing,
so that users can concern themselves with the acutal structure of the
data.

The basic pretty-printable objects are 'str', 'int', and 'float'.
If 'None' is pretty-printed, it is formatted as nothing.  Pretty-printable
objects may be composed into more complex documents, while determining the
indentation and positioning of sub-documents, with functions such
as 'abut', 'space', 'stack' and 'nest'.

These functions are modeled after the pretty-printer combinators in the
Haskell library Text.PrettyPrint.HughesPJ.  
"""

# Pretty-printing classes in this file have lowercase types, since they are
# used like functions.

import sys
import cStringIO
import codecs

# UTF-8 encoder
_utf8enc = codecs.getencoder('UTF-8')

# Number of columns in output
_COLUMNS = 80

# The following interface is followed by pretty-printing code, including
# '_prettyPrint' and the 'format' methods of pretty instances.
# The parameters are a posinfo object and a file.
# The return value is None for an empty document,
# or an interval (start, end) for a nonempty document

# These functions are used in the 'pre' slot of 'posinfo'

# Do nothing.
def _printNothing(file, pos):
    return pos

# Print a space.
def _printOneSpace(file, pos):
    if file: file.write(' ')
    return posinfo(pos.indent, pos.column + 1)

# Move the indentation to the current starting position.
def _ratchet(file, pos):
    return posinfo(pos.column, pos.column)

# Print a newline and some indentation.
def _printNewlineIndent(file, pos):
    ind = pos.indent
    if file: file.write('\n' + ' ' * ind)
    return posinfo(ind, ind)

# Print with extra indentation
def _indentBy(indent):
    def do_it(file, pos):
        new_indent = pos.indent + indent

        # If we haven't reached the right indentation level, then add extra
        # spaces
        if pos.column < new_indent:
            extra_indent = new_indent - pos.column
            if file: file.write(' ' * extra_indent)
            
            return posinfo(new_indent, new_indent)
        else:
            return posinfo(new_indent, pos.column)

    return do_it

# Go to the given column; insert at least one space.
# If past that column, start a new line.
# The given column becomes the new indentation level.
def _goToColumnOneSpace(indent):
    def do_it(file, pos):
        delta = indent - pos.column
        if file:
            if delta > 0:               # Fits on current line
                file.write(' ' * delta)
            else:                       # Go to next line
                file.write('\n' + ' ' * indent)

        return posinfo(indent, indent)
    return do_it

class posinfo(object):
    """Positioning information for pretty-printing.

    indent: Indentation to give to the first document in subsequent lines
    column: Position of the next character to be printed on the current line
    pre: Action to perform before printing something
       pre(file, pos) -> new_pos
          Update position in preparation to write something.
          If file is not None, then write output to the file so that
          output will print at the right place."""
    def __init__(self, indent, column, pre = _printNothing):
        self.indent = indent
        self.column = column
        self.pre = pre

    def addPre(self, new_pre):
        """Add another preformatter.  It will run after existing
        preformatters."""
        old_pre = self.pre
        def composed_pre(file, pos):
            return new_pre(file, old_pre(file, pos))

        return posinfo(self.indent, self.column, composed_pre)

    __slots__ = ['indent', 'column', 'pre']

# Top-level pretty-printing function.
# This calls the internal function and returns None.
def render(doc, file = sys.stdout):
    "Write a pretty-printable object to a file."
    _prettyPrint(doc, file)

def renderString(doc):
    "Render a pretty-printable object as a string."
    buf = cStringIO.StringIO()
    _prettyPrint(doc, buf)
    ret = buf.getvalue()
    buf.close()
    return ret

def _prettyPrint(doc, file = sys.stdout, pos = posinfo(0, 0)):
    if isinstance(doc, basestring): # string
        return _prettyPrintText(doc, file, pos)
    elif isinstance(doc, pretty):       # pretty instance
        return doc.format(file, pos)
    elif isinstance(doc, (int, float)): # showable as a string
        return _prettyPrintText(str(doc), file, pos)
    elif doc is None:                   # Empty document
        return None

    else:
        raise TypeError, type(doc)

# All pretty-printing (other than whitespace) goes through this function
def _prettyPrintText(text, file, pos):
    "Print a string and update position information."

    # Encode UTF-8 text for display
    if isinstance(text, unicode): text_bytes, _ = _utf8enc(text)
    else: text_bytes = text

    pos = pos.pre(file, pos)            # Run preformatter
    file.write(text_bytes)              # Write string
    start = pos.column                  # Get starting position
    end = start + len(text)             # Compute ending position
    return (start, end)                 # Return interval

###############################################################################
# Pretty-printers

class pretty(object):
    def __new__(self, *args, **kwargs):
        # Special-case pretty instances, strings, and None
        # so that we can use pretty as a type-cast operator
        if self is pretty and len(args) == 1 and len(kwargs) == 0:
            arg = args[0]
            if isinstance(args[0], pretty):
                return args[0]
            elif isinstance(args[0], basestring):
                return args[0]
            elif args[0] is None:
                return None

        return object.__new__(self, *args, **kwargs)

    def __init__(self, arg):
        raise NotImplementedError, "'pretty' is an abstract base class"

    def format(self, file, pos):
        """An internal formatting routine.  Do not call this directly;
        call 'render' or 'renderString' instead.

        file: output file
        pos: formatting information

        returns a boolean telling whether this document is empty"""
        raise NotImplementedError

    def render(self, file = sys.stdout):
        """Render this object to a file"""
        # Call the global function
        render(self, file)

    def renderString(self):
        """Render this object to a string"""
        return renderString(self)

class _grouping(pretty):
    """A grouping of pretty-printable documents"""

    def __init__(self, *argl):
        if len(argl) == 2:
            self.documents = argl
        elif len(argl) == 1:
            self.documents = argl[0]
        else:
            raise TypeError, "expecting sequence or two printables"

    @staticmethod
    def _updatePosition(pos, cur_start, cur_end):
        """Update the formatting information to pass to children.
        This should return a new 'pos' object.
        The new object's column should always be 'cur_end'."""
        raise NotImplementedError

    @staticmethod
    def _setup(pos):
        """Set up formatting.  By default, this does nothing."""
        return pos

    def format(self, file, pos):
        # Print all elements
        any_is_nonempty = False
        pos = self._setup(pos)
        for doc in self.documents:
            ret = _prettyPrint(doc, file, pos)

            # If doc was not empty, then update positioning info
            if ret is not None:
                (cur_start, cur_end) = ret
                
                if not any_is_nonempty:
                    # This is the first nonempty element.
                    # Keep track of its starting position.
                    start = cur_start
                    any_is_nonempty = True

                pos = self._updatePosition(pos, cur_start, cur_end)

        # Return the printed interval
        if any_is_nonempty:
            return (start, cur_end)
        else:
            return None

class abut(_grouping):
    """abut(x, y) -> print x and y adjacently, with no intervening space
    abut(sequence) -> print all elements of the sequence adjacently"""

    @staticmethod
    def _updatePosition(pos, cur_start, cur_end):
        # Next document is printed right after current document
        return posinfo(pos.indent, cur_end, _printNothing)

class space(_grouping):
    """space(x, y) -> print x and y with an intervening space
    space(sequence) -> print all elements of the sequence adjacently"""

    @staticmethod
    def _updatePosition(pos, cur_start, cur_end):
        # Next document is printed after current document, with one space
        return posinfo(pos.indent, cur_end, _printOneSpace)

class stack(_grouping):
    """stack(x, y) -> print y under x with the same indentation
    stack(sequence) -> print all elements of the sequence starting
        on separate lines, with the same indentation as the first element"""

    @staticmethod
    def _setup(pos):
        return pos.addPre(_ratchet)

    @staticmethod
    def _updatePosition(pos, cur_start, cur_end):
        # Locally, set indentation to the first document's starting position
        # Next document is printed on a new line
        return posinfo(cur_start, cur_end, _printNewlineIndent)

class nest(pretty):
    """
    nest(doc, indentation) -> print 'doc' with additional indentation
       relative to its context
    """

    def __init__(self, doc, indent):
        self.indentation = indent
        self.doc = doc

    def format(self, file, pos):
        # Print contents with extra indentation
        _prettyPrint(self.doc, file, pos.addPre(_indentBy(self.indentation)))

class hang(pretty):
    """
    hang(doc1, indent, doc2) -> print 'doc1', followed by indented 'doc2'
       on the same line if it fits, on the next line otherwise
    """

    def __init__(self, doc1, indent, doc2):
        self.doc1 = doc1
        self.indentation = indent
        self.doc2 = doc2

    def format(self, file, pos):
        rc = _prettyPrint(self.doc1, file, pos)

        if rc is None:
            # When first document is empty, behave like 'nest'
            return _prettyPrint(nest(self.doc2, self.indentation), file, pos)
        else:
            # Otherwise, indent the second part
            (fst_start, fst_end) = rc
            pos = posinfo(fst_start, fst_end,
                          _goToColumnOneSpace(fst_start + self.indentation))
            return _prettyPrint(self.doc2, file, pos)

class linewr(pretty):
    """
    linewr(doc1, doc2, indent) -> print 'doc1', then, print 'doc2' on the 
    same line if it fits, and on the next line with a relative indentation 
    of 'indent' if it does not.
    """

    def __init__(self, doc1, doc2, indent = 2):
        self.doc1 = doc1
        self.indentation = indent
        self.doc2 = doc2

    def format(self, file, pos):
        rc = _prettyPrint(self.doc1, file, pos)
        
        if rc is None:
            #if the first part didn't exist, just print
            return _prettyPrint(self.doc2, file, pos)
        else:
            #Otherwise, check to see if there's room on this line
            (fst_start, fst_end) = rc
            doc2str =  renderString(self.doc2)
            if doc2str.count('\n') == 0:
                strlen = len(doc2str)
            else:
                strlen = doc2str.index('\n')

            pos = posinfo(fst_start, fst_end)
            if strlen < _COLUMNS - fst_end:
                #It's fine, print on this line
                _prettyPrint(self.doc2, file, pos)
            else:
                #Too big, print on next
                _prettyPrint(self.doc2, file, pos.addPre(_printNewlineIndent))

def punctuate(separator, documents):
    """punctuate(separator, sequence) -> sequence with separator interspersed"""

    return [abut(doc, separator) for doc in documents[:-1]] + documents[-1:]

def parens(doc):
    """parens(doc) -> "(" doc ")" """
    return abut(["(", doc, ")"])

def braces(doc):
    """braces(doc) -> "{" doc "}" """
    return abut(["{", doc, "}"])

def brackets(doc):
    """brackets(doc) -> "[" doc "]" """
    return abut(["[", doc, "]"])

def parensStack(documents, indent = 2):
    """parens(documents) -> print stacked documents with surrounding parentheses"""
    return stack(["(", nest(stack(documents), indent), ")"])

def bracesStack(documents, indent = 2):
    """braces(documents) -> print stacked documents with surrounding braces"""
    return stack(["{", nest(stack(documents), indent), "}"])

def bracketsStack(documents, indent = 2):
    """brackets(documents) -> print stacked documents with surrounding brackets"""
    return stack(["[", nest(stack(documents), indent), "]"])
