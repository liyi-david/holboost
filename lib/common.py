# here are some assisting functions

def all_are_same_instances(objects, classes):
    if len(objects) == 0:
        return True

    # all instances have to be samely typed
    for obj in objects:
        if type(obj) != type(objects[0]):
            return False

    return isinstance(objects[0], classes)

def one_of_them_is(objects, classes):
    if len(objects) == 0:
        return False

    for obj in objects:
        if isinstance(obj, tuple(classes)):
            return True

    return False

def code_indent(code, level, indent='  ', forceEndl=False):
    """
    this function add indents to each line in a code block. the added indent is `indent * level`.
    if level < 0, it reduce indents from each line
    """

    lines = code.split('\n')
    if level > 0:
        result = "\n".join(map(lambda line: indent * level + line, lines))
    elif level < 0:
        raise Exception('unimplemented')

    if forceEndl and result[-1] != "\n":
        result += "\n"

    return result
