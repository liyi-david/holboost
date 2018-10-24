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
