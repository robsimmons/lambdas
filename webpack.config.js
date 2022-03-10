module.exports = {
    mode: 'development',
    entry: './src/main.js',
    resolve: {
	modules: [ './generated/agda' ],
    }
};
