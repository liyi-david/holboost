class IdManager:
    """
    IdManager is not thread_safe
    """

    def _init__(self):
        self.base_id = -1

    def alloc(self):
        self.base_id += 1
        return self.base_id
