local function choose(value, fallback)
    return value or fallback
end

return {
    title = "A small LuaJIT example",
    count = 3,
    choose = choose,
}
