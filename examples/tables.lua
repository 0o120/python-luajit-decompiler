local defaults = {
    enabled = true,
    limit = 10,
    label = "shared",
}

local metadata = {
    __index = function(_, key)
        local value = defaults[key]
        if value then
            return value
        end
        error("Missing field: " .. tostring(key))
    end,
}

local rows = {
    [1] = {id = 1},
    [2] = {id = 2, limit = 20},
    [3] = {id = 3, enabled = false, label = "custom"},
}

for _, row in pairs(rows) do
    setmetatable(row, metadata)
end

return rows
